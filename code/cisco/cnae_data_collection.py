'''
///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                                                                           //
// Candid Offline Data Collection Tool For ACI/Standalone                    //
//                                                                           //
//                                                                           //
// Date: 09/27/2016                                                          //
// Author: chnagara@                                                         //
//                                                                           //
// Copyright Cisco Systems [2015 - *] (Candid Alpha Project)                 //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
'''

from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

__default_version__ = "Local Build"

_APIC = "APIC"
_STANDALONE = "STANDALONE"
_MSO = "MSO"
global_nat_box = None

import json
import hashlib
import csv
import requests
from requests.auth import HTTPBasicAuth
import os
import argparse
import subprocess
import getpass
import math
import xml.etree.cElementTree as ET
from multiprocessing.dummy import Pool as ThreadPool
import threading
import paramiko
import sys
import gzip
import tempfile
import tarfile
import shutil
from requests.packages.urllib3.exceptions import InsecureRequestWarning
requests.packages.urllib3.disable_warnings(InsecureRequestWarning)
from cryptography.hazmat.backends import default_backend
from time import gmtime, strftime
from functools import wraps
import traceback
import re
import time
from socket import gethostbyname, gethostbyaddr, getaddrinfo
import setuptools
import zlib
import importlib
import ssl
import atexit
from enum import Enum
from string import Template
import io
import datetime
import six

SUPPORTED_ACI_VERSIONS = [
    '1.2',
    '1.3',
    '2.0',
    '2.1',
    '2.2',
    '2.3',
    '3.0',
    '3.1',
    '3.2',
    '4.0',
    '4.1',
    '4.2',
    '5.0',
    '5.1',
    '5.2'
]

SUPPORTED_DCNM_VERSIONS = [
    '11.2',
    '11.3',
    '11.4',
    '11.5',
    '11.5.1',
    '12.0'
]

SUPPORTED_SWITCH_VERSIONS = [
    '11.2',
    '11.3',
    '12.0',
    '12.1',
    '12.2',
    '12.3',
    '13.0',
    '13.1',
    '13.2',
    '14.0',
    '14.1',
    '14.2',
    '15.0',
    '15.1',
    '15.2']

SUPPORTED_NXFABRIC_SWITCH_VERSIONS = [
    '9.3',
    '10.1']

NODE_TIMEOUT_STR = "Collection failure due to node timeout"
COLLECTION_ABORTED_STR = "Collection has been aborted, skipping %s query : %s"
REQUEST_PIPELINE_DEPTH = 1
STANDALONE_REQUEST_PIPELINE_DEPTH = 2
COOKIE_EXPIRED_STR = "Cookie expired"

CONFIG_EXPORT_POLICY_FAILURE = "Config export job on apic cannot be configured"
CONFIG_EXPORT_POLICY_NOT_CONFIGURED = "Config export job not configured on APIC"
CONFIG_EXPORT_POLICY_ID_NOT_CONFIGURED = "Config export job trigger time cannot be found"
CONFIG_EXPORT_POLICY_STATUS_NOT_SUCCESS = "Config export job did not run sucessfully"
CONFIG_EXPORT_SNAPSHOT_NOT_DELETED = "Config export snapshot was not deleted successfully"
CONFIG_EXPORT_RETRY_COUNT = 2
# Time in seconds between polling for job status
CONFIG_EXPORT_RETRY_INTERVAL = 10
CONFIG_EXPORT_SFTP_FILE_PATH_NOT_FOUND = "Remote path for config export not found"

COLLECTION_CONFIG_OPTIONS_FILENAME = "collectionOptionsConfiguration.json"

AUDIT_LOG_ELAPSED_HISTORY_HOURS = 24
MSO_TENANTS_PER_POLICY_REPORT = 1

# node roles
CONTROLLER = "controller"
LEAF = "leaf"
SPINE = "spine"
DCNM = "dcnm"
MSO = "mso"
STANDALONE_SPINE = "standalone_spine"
STANDALONE_LEAF = "standalone_leaf"
VCENTER = "vcenter"
NETSCALER = "netscaler"
F5 = "f5"
COMMAND_NODE = "command_node"
ACI_ROLES = [SPINE, LEAF, CONTROLLER]
STANDALONE_ROLES = [STANDALONE_LEAF, STANDALONE_SPINE, DCNM]
THIRD_PARTY_ROLES = [VCENTER, NETSCALER, F5]
UNSUPPORTED = "UNSUPPORTED"

NAE_APP_LOCAL_IP = "172.17.0.1"
NAE_APP_LOCAL_POD_ID = 0

F5_ACCESS = "rest"
MAX_WAIT_COUNT = 10
SSH_TIMEOUT_SLEEP_TIME = 10

def candidTimeIt(function):
    @wraps(function)
    def functionTimer(*args, **kwargs):
        t0 = time.time()
        result = function(*args, **kwargs)
        t1 = time.time()
        print("Total Candid Collection time  %s: %s seconds" %\
            (function.__name__, str(t1 - t0)))
        return result
    return functionTimer

def safely_decode_str(str_val):
    if isinstance(str_val, str):
        return str_val
    else:
        return str_val.decode("utf-8")

def safely_encode_str(str_val):
    if isinstance(str_val, bytes):
        return str_val
    else:
        return str_val.encode("utf-8")

class CollectionConfigurationGenerator:
    def __init__(self, logger, args):
        self.args = args
        if self.args and self.args.get("nat"):
            try:
                with open(self.args["nat"], "r") as f:
                    nat_json = json.load(f)
                    self.nat_configuration_list = nat_json.get("natConfiguration")
                    logger.debug(
                        "Loaded NAT json configuration file successfully in CollectionConfigurationGenerator!")
            except Exception as e:
                logger.debug(
                    "NAT json configuration file was not loaded into CollectionConfigurationGenerator")
                raise e
        else:
            self.nat_configuration_list = None

    def __str__(self):
        phrase = {}
        for arg in self.args:
            if arg == "nat" and self.args[arg]:
                phrase["nat"] = self.nat_configuration_list
            else:
                phrase[arg] = self.args[arg]
        first_entity = {"collectionEntities":[phrase]}

        return json.dumps(first_entity, indent=4, sort_keys=True)

    def getNatJsonEntries(self):
        return self.nat_configuration_list

    def createJson(self):
        fileName = COLLECTION_CONFIG_OPTIONS_FILENAME
        with open(fileName, "w") as f:
            f.write(self.createCollectionEntityConfiguration())

    def copy_key_to_collection_entity(self, key, collection_entity):
        key_value = self.args.get(key)
        if key_value:
            collection_entity[key] = key_value

    #Normalize the user configured options into collectionConfigurationOptions
    def createCollectionEntityConfiguration(self):
        output_dict = { }
        collectionEntity  = { }
        copy_key = lambda x: self.copy_key_to_collection_entity(x, collectionEntity)
        collectionEntity['entityIps'] = self.args.get("entityIps")
        if self.args.get("cnaeMode") == _APIC:
             collectionEntity['entityType'] = "aci-fabric"
        elif self.args.get("cnaeMode") == _MSO:
             collectionEntity['entityType'] = "mso"
        else:
             collectionEntity['entityType'] = "nx-fabric"
        if self.args.get("cnaeMode") == _STANDALONE:
            collectionEntity['siteName'] = self.args.get("siteName")
            collectionEntity['loopbackInterface'] = self.args.get("loopbackInterface", -1)
        collectionEntity["entityFlags"] = { "isConfigurationExportPolicyEnabled": False,
                                             "isNatEnabled": False}
        if self.args.get('apicConfigExportPolicyName') and self.args.get('apicConfigExportFormat'):
            collectionEntity["entityFlags"]['isConfigurationExportPolicyEnabled'] = True
            collectionEntity["entityConfigurationExportPolicy"] = { }
            collectionEntity["entityConfigurationExportPolicy"]["exportPolicyName"] = self.args.get('apicConfigExportPolicyName')
            collectionEntity["entityConfigurationExportPolicy"]["exportFormat"] = self.args.get("apicConfigExportFormat")

        copy_key("connectionPreferencePrimary")
        copy_key("connectionPreferenceSecondary")

        if self.args.get('nat'):
             collectionEntity["entityFlags"]["isNatEnabled"] = True
             collectionEntity["entityNatConfiguration"] = self.getNatJsonEntries()

        if self.args.get("thirdPartyServiceContext"):
            collectionEntity["thirdPartyServiceContext"] = self.args.get("thirdPartyServiceContext").getServiceRegistry()

        output_dict["collectionEntities"] = [collectionEntity]
        return json.dumps(output_dict, indent=4, sort_keys=True)

    def get(self, attr, default_value=None):
        return self.args.get(attr, default_value)

    # can also be used to set argument
    def add(self, key, value):
        self.args[key] = value

    @staticmethod
    def parseCollectionOptionsConfiguration(logger, collectionOptionsConfiguration):
        if collectionOptionsConfiguration:
            try:
                json_contents = json.loads(collectionOptionsConfiguration)
                first_entity = json_contents.get("collectionEntities")[0]
                parsedCollectionOptionsConfiguration = {}
                parsedCollectionOptionsConfiguration['entityType'] = first_entity.get("entityType")
                parsedCollectionOptionsConfiguration['entityIps'] = first_entity.get("entityIps")
                parsedCollectionOptionsConfiguration['entityFlags'] = first_entity.get("entityFlags")
                parsedCollectionOptionsConfiguration['entityConfigurationExportPolicy'] = first_entity.get("entityConfigurationExportPolicy")
                parsedCollectionOptionsConfiguration['siteName'] = first_entity.get("siteName")
                parsedCollectionOptionsConfiguration['fabricUserName'] = first_entity.get("fabricUserName")
                parsedCollectionOptionsConfiguration['fabricPassword'] = first_entity.get("fabricPassword")
                parsedCollectionOptionsConfiguration['lanUsername'] = first_entity.get("lanUsername")
                parsedCollectionOptionsConfiguration['lanPassword'] = first_entity.get("lanPassword")

                parsedCollectionOptionsConfiguration['leafList'] = {}
                if 'leafEntityList' in first_entity :
                    for leaf_entity in first_entity.get("leafEntityList") :
                        leaf_unpw_data = {}
                        leaf_unpw_data['userName'] = leaf_entity.get("leafUserName")
                        leaf_unpw_data['passWord'] = leaf_entity.get("leafPassword")
                        parsedCollectionOptionsConfiguration['leafList'][leaf_entity.get("leafIpAddress")] = leaf_unpw_data
                parsedCollectionOptionsConfiguration['loopbackInterface'] = first_entity.get("loopbackInterface")
                return parsedCollectionOptionsConfiguration
            except Exception as e:
                logger.warning(
                    "Configuration options parse error, please check file: {0}".format(
                        collectionOptionsConfiguration))
                raise e

class NatTranslatorException(Exception):
    pass

class NatTranslator:

    class NatNode:

        def __init__(self, node_entry):
            self.public_port, self.private_port = [None]*2
            self.public_ip, self.private_ip = self.convertEntryToNode(
                node_entry)

        def convertEntryToNode(self, entry):
            public_ip = entry.get("publicIp")
            private_ip = entry.get("privateIp")
            return public_ip, private_ip

        def __repr__(self):
            public = {}
            public["ip"] = self.public_ip
            public["port"] = self.public_port

            private = {}
            private["ip"] = self.private_ip
            private["port"] = self.private_port

            phrase = {"public": public, "private": private}
            return json.dumps(phrase, indent=4, sort_keys=True)

    def __init__(self, logger, nat_configuration_list=None):
        self.public_to_private_translation = {}  # input ips : NatNode
        self.private_to_public_translation = {}  # nat translations : NatNode
        # list of dictionaries with public/private ips
        self.nat_configuration_list = nat_configuration_list
        if nat_configuration_list:
            self.populateConvertors()
            logger.info(
                "Uploading from NAT json successful! Configuring NAT complete.")
        else:
            logger.info(
                "No NAT configuration file was specified. NAT is disabled.")

    # populates forwards convertor and backwards convertor
    # populates convertors
    # validates nat_json entries
    def populateConvertors(self):
        for array_index, nat_entry in enumerate(self.nat_configuration_list):
            nat_node = NatTranslator.NatNode(nat_entry)
            if self.isNatEntryValid(nat_node, array_index):
                self.public_to_private_translation[str(nat_node.public_ip)] = nat_node
                self.private_to_public_translation[str(nat_node.private_ip)] = nat_node

    # check if nat_node is valid and should be added to nat convertors
    def isNatEntryValid(self, nat_node, array_index):
        indexMsg = "array index ({0}) has ".format(array_index)

        if None in [nat_node.private_ip, nat_node.public_ip]:
            raise NatTranslatorException(
                    indexMsg+"entry missing publicIp, privateIp, or both key(s)")
        elif nat_node.private_ip == nat_node.public_ip:
            raise NatTranslatorException(
                    indexMsg+"same private_ip and public_ip (%s)"%(
                    nat_node.private_ip))
        # need to check if private/public ip is duplicated
        public_to_private_keys = list(self.public_to_private_translation.keys())
        private_to_public_keys = list(self.private_to_public_translation.keys())
        for nat_ip in [nat_node.private_ip, nat_node.public_ip]:
            if nat_ip in public_to_private_keys:
                raise NatTranslatorException(
                    indexMsg+"ip (%s) which already exists as public_ip"%nat_ip)
            elif nat_ip in private_to_public_keys:
                raise NatTranslatorException(
                    indexMsg+"ip (%s) which already exists as private_ip"%nat_ip)
        return True

    # input public_ip:port and receive nat inputs
    def get_public_to_private_translation(self, ip, port=None):
        node = self.public_to_private_translation.get(
            ip)  # returns none if ip is not in dictionary
        if node is None:
            return ip, port
        return node.private_ip, node.private_port

    # input ip:port and receive nat translations to node attributes
    def get_private_to_public_translation(self, ip, port=None):
        node = self.private_to_public_translation.get(
            ip)  # returns none if ip is not in dictionary
        if node is None:
            return ip, port
        return node.public_ip, node.public_port

    def __repr__(self):
        phrase = "["
        dic = self.public_to_private_translation
        for ip in dic:
            phrase = phrase + str(dic[ip]) + ","
        return phrase[:-1] + "]"


class ExceptionUtils:

    '''
        log traceback (stack and exeption) at a certain log level
    '''
    @staticmethod
    def createTraceback(stacktrace_stack_list):
        '''
        stacktrace_stack_list is a list of str, where each str contains 2 lines
        split each str into 2 str, such that each str contains one line
        '''

        flattened_list_of_lines = ["= = = BEGINNING TRACEBACK = = =\n"] + stacktrace_stack_list
        stacktrace_exc = traceback.format_exc()
        if stacktrace_exc:
            flattened_list_of_lines += ["--------------\n"] + [stacktrace_exc]
        flattened_list_of_lines += ["= = = END OF TRACEBACK = = ="]
        return ''.join(flattened_list_of_lines)

    @staticmethod
    def isTimeoutException(trace):
        if "SSHException: Timeout opening channel." in trace:
            return True
        if "socket.timeout" in trace:
            return True
        return False


class GlobalUtils:

    @staticmethod
    def generateNodeId(node_name, node_ids):
        node_hash = hashlib.md5(node_name.encode())
        node_id = int(node_hash.hexdigest(), 16) % (pow(2,31)-1)
        while True:
            if node_id in node_ids:
                node_id += 1
            else:
                node_ids.add(node_id)
                return node_id

    @staticmethod
    def getVersion(
            logger,
            version_file_dir="",
            version_file_name='version.properties'):
        version = __default_version__
        if not version_file_name:
            version_file_name = 'version.properties'
        try:
            (candid_version, candid_ova_version) = (None, None)
            with open(version_file_dir + '/' + version_file_name, 'r') as f:
                lines = f.readlines()
            for line in lines:
                if 'candid.version' in line:
                    candid_version = line.split('=')[1]
                    candid_version = " ".join(candid_version.split())
                if 'candid.ova.version' in line:
                    candid_ova_version = line.split('=')[1]
                    candid_ova_version = " ".join(candid_ova_version.split())
            if ((candid_version is not None) and (
                    candid_ova_version is not None)):
                version = candid_version + '.' + candid_ova_version
            else:
                raise CandidDataCollectionException(
                    "Candid version or ova version not present in version file.")
        except IOError:
            logger.warning(
                "IOError for file: " +
                version_file_dir +
                '/' +
                version_file_name)
        except Exception as e:
            traceback.print_stack()
            print('--------------')
            traceback.print_exc()
            logger.warning(
                ("Unable to get version from version.properties.Reson::%s" %
                 str(e)))
        return version

    @staticmethod
    def gzipDecompress(cls, compressed_data):
        result = None
        try:
            result = zlib.decompress(compressed_data, zlib.MAX_WBITS | 32)
        except Exception as e:
            raise Exception("Decompression error %s" % str(e))
        return result

    @staticmethod
    def isIpv6(ip):
        return ":" in ip


class ParseUtils:

    @staticmethod
    def findAll(cls, query_response, match_criteria):
        results = []
        xml_doc = ET.fromstring(query_response)
        results = xml_doc.findall(match_criteria)
        return results

    @staticmethod
    def getChildren(cls, query_response, match_criteria):
        results = []
        json_doc = json.loads(query_response)
        imdata = json_doc['imdata']
        for each_json in imdata:
            if match_criteria in each_json:
                results.append(each_json)
        return results

    @staticmethod
    def getAttribute(cls, obj, key, optional=False):
        value = None
        try:
            if isinstance(obj, type(ET.Element("root"))):
                value = str(obj.attrib[key])
            else:
                value = str(obj["attributes"][key])
        except BaseException:
            if optional:
                return None
            else:
                raise AttributeError("Attribute missing", key, str(obj))
        return value


class DcnmVersionApiUtils:
    # add new apis depending version here
    BEFORE_V12_API = ""
    V12_API = "/appcenter/cisco/ndfc/api/v1"

    @staticmethod
    def getSampleVersionForApis():
        return ["11.0", "12.0"]

    @staticmethod
    def isV12Query(query_cmd):
        return DcnmVersionApiUtils.V12_API in query_cmd

    def _parseVersion(function):
        @wraps(function)
        def checkVersion(version):
            try:
                num = float(version)
            except ValueError:
                return function(None)
            return function(num)
        return checkVersion

    @staticmethod
    @_parseVersion
    def getPrefixApi(version):
        if not version or version < 12.0:
            return DcnmVersionApiUtils.BEFORE_V12_API
        else:
            return DcnmVersionApiUtils.V12_API

    @staticmethod
    @_parseVersion
    def getLoginSession(version):
        if not version or version < 12.0:
            return DCNMLoginSession
        else:
            return NDFCLoginSession



class CandidDataCollectionException(Exception):
    pass


class TopologyExplorerException(Exception):
    pass


class CandidPartialDataCollectionException(Exception):
    pass


'''
This defines 3rd-party vendors we support
'''


class Vendor(Enum):
    VM_WARE = 1
    CITRIX_NETSCALER = 2
    F5 = 3
    MICROSOFT = 4
    OPEN_STACK = 5
    CISCO_NAE = 6


'''
This defines different types of product offered by the vendors
'''


class Product(Enum):
    VMM = 1
    LOADBALANCER = 2
    FIREWALL = 3
    NAE_LITE = 4


'''
This is the base class for all third-party service API implementations
'''


class ThirdPartyAPIBase(object):

    @staticmethod
    def readPassword(svc_dic):
        try:
            desc = svc_dic['desc'] if 'desc' in svc_dic else svc_dic['type']
            host = svc_dic['host']
            user = svc_dic['user']
            print('Enter password for {}: {}, user: {}'.format(
                desc, host, user))
            svc_dic['password'] = getpass.getpass()
        except Exception as e:
            raise CandidDataCollectionException(
                'Please enter password: ' + str(e))

    '''
    Override in derived class to support additional arguments
    '''
    @staticmethod
    def parseArguments(arg_dic, svc_ctx):
        try:
            svc_dic = arg_dic.copy()
            svc_dic.update({'queryIds': parseQueryIds(
                svc_dic['queryIds'] if 'queryIds' in svc_dic else '')})
            svc_ctx.registerService(svc_dic)
            return svc_dic
        except KeyError as e:
            raise CandidDataCollectionException(
                'Malformed third-party service arguments: {}'.format(str(e)))

    '''
    Must override in a derived class to augment with specific requirements
    '''
    @staticmethod
    def getTopoNode(svc_dic):
        node = Node(svc_dic['host'])
        node.node_name = svc_dic['entityName']
        node.node_is_login = svc_dic['is_login']
        node.node_is_supported = svc_dic['is_supported']
        svc_dic['adminConfig'] = {}
        svc_dic['adminConfig'].update({'host': svc_dic['host']})
        if 'chassisId' in svc_dic:
            svc_dic['adminConfig'].update({'chassisId': svc_dic['chassisId']})
        svc_dic['adminConfig'].update({'entityName': svc_dic['entityName']})
        if 'aeOnboardingInfos' in svc_dic:
            svc_dic['adminConfig'].update({'aeOnboardingInfos': svc_dic['aeOnboardingInfos']})
        node_admin_config = json.dumps(svc_dic['adminConfig']) if 'adminConfig' in svc_dic else ''
        node.node_admin_config = node_admin_config.encode("utf-8")
        return node

    '''
    May implement in derived class if required
    '''
    @staticmethod
    def checkModuleVersion():
        return '', '', True  # Module name, expected version, True if installed False otherwise

    '''
    May implement in derived class if required
    '''
    @classmethod
    def loadModules(cls):
        pass

    '''
    Check sanity of a given service
    '''
    @staticmethod
    def checkSanity(svc_dic):
        svc_dic.update({'is_login': False})
        svc_dic.update({'is_supported': True})


'''
This is the top-level API for vCenter data collection
'''


class VCenterAPI(ThirdPartyAPIBase):

    SUPPORTED_PYVMOMI_VERSION = '6.5.0.2017.5.post1'

    @staticmethod
    def parseArguments(arg_dic, svc_ctx):
        try:
            svc_dic = ThirdPartyAPIBase.parseArguments(arg_dic, svc_ctx)
            svc_dic.update({'desc': 'vCenter'})
        except KeyError as e:
            raise CandidDataCollectionException(
                'Malformed third-party service arguments: {}'.format(str(e)))

    @staticmethod
    def getTopoNode(svc_dic):
        node = ThirdPartyAPIBase.getTopoNode(svc_dic)
        node.node_id = SyntheticNodeIdProvider.getNodeId(
            Vendor.VM_WARE.value, Product.VMM.value, svc_dic['id'])
        node.node_dn = 'topology/vcenter/node-{}'.format(node.node_id)
        node.node_role = 'vcenter'
        return node

    @staticmethod
    def checkModuleVersion():
        try:
            import pkg_resources
            valid = pkg_resources.get_distribution(
                'pyVmomi').version == VCenterAPI.SUPPORTED_PYVMOMI_VERSION
        except BaseException:
            valid = False
        return 'pyVmomi', VCenterAPI.SUPPORTED_PYVMOMI_VERSION, valid

    @classmethod
    def loadModules(cls):
        try:
            pyvim_conn = importlib.import_module('pyVim.connect')
            pyvmomi = importlib.import_module('pyVmomi')
            cls.VCENTER_CLASS_CONNECT = staticmethod(
                getattr(pyvim_conn, 'SmartConnect'))
            cls.VCENTER_CLASS_DISCONNECT = staticmethod(
                getattr(pyvim_conn, 'Disconnect'))
            cls.VCENTER_MODULE_VIM = getattr(pyvmomi, 'vim')
        except ImportError as e:
            raise CandidDataCollectionException(
                "Error while importing third-party modules. {}".format(str(e)))

    @staticmethod
    def checkSanity(svc_dic):
        ThirdPartyAPIBase.checkSanity(svc_dic)
        svc_dic.update({'is_login': VCenterAPI.checkServiceLogin(svc_dic)})

    @staticmethod
    def checkServiceLogin(svc_dic):
        try:
            client = VCenterClient(
                svc_dic['host'],
                svc_dic['user'],
                svc_dic['password'],
                None)
            client.close()
            login = True
        except BaseException:
            login = False
        return login


'''
vCenter data structures
Note: Class member names in these structures need to be in camelcase (out of convention)
      to make generated JSON objects have camelcase names.
'''


class VCenterBaseClass(object):

    def toJSON(self):
        return json.dumps(
            self,
            default=lambda o: o.__dict__,
            sort_keys=True,
            indent=4)


class VCenter(VCenterBaseClass):

    def __init__(self):
        super(VCenter, self).__init__()
        self.host = None
        self.version = None
        self.datacenters = []

    def setHost(self, host):
        self.host = host

    def setVersion(self, version):
        self.version = version

    def addDatacenter(self, datacenter):
        self.datacenters.append(datacenter)


class Datacenter(VCenterBaseClass):

    def __init__(self):
        super(Datacenter, self).__init__()
        self.name = None
        self.hypervisors = []
        self.distributedVirtualSwitches = []
        self.virtualMachines = []

    def setName(self, name):
        self.name = name

    def addHypervisor(self, hypervisor):
        self.hypervisors.append(hypervisor)

    def addDvs(self, dvs):
        self.distributedVirtualSwitches.append(dvs)

    def addVm(self, vm):
        self.virtualMachines.append(vm)


class Hypervisor(VCenterBaseClass):

    def __init__(self):
        super(Hypervisor, self).__init__()
        self.name = None
        self.physicalNics = []
        self.network = None

    def setName(self, name):
        self.name = name

    def addPhysicalNic(self, pnic):
        self.physicalNics.append(pnic)

    def setNetwork(self, net):
        self.network = net


class HypervisorNetwork(VCenterBaseClass):

    def __init__(self):
        super(HypervisorNetwork, self).__init__()
        self.dnsConfig = None

    def setDnsConfig(self, dnsconfig):
        self.dnsConfig = dnsconfig


class HypervisorDnsConfig(VCenterBaseClass):

    def __init__(self):
        super(HypervisorDnsConfig, self).__init__()
        self.hostName = None
        self.domainName = None

    def setHostName(self, hostname):
        self.hostName = hostname

    def setDomainName(self, domainname):
        self.domainName = domainname


class PhysicalNic(VCenterBaseClass):

    def __init__(self):
        super(PhysicalNic, self).__init__()
        self.deviceName = None
        self.macAddress = None
        self.ipAddress = None

    def setDeviceName(self, device_name):
        self.deviceName = device_name

    def setMacAddress(self, mac_address):
        self.macAddress = mac_address

    def setIpAddress(self, ip_address):
        self.ipAddress = ip_address


class Dvs(VCenterBaseClass):

    def __init__(self):
        super(Dvs, self).__init__()
        self.name = None
        self.linkDiscoveryProtocol = 0
        self.portGroups = []

    def setName(self, name):
        self.name = name

    def setLdp(self, ldp):
        self.linkDiscoveryProtocol = ldp

    def addPortGroup(self, port_group):
        self.portGroups.append(port_group)


class PortGroup(VCenterBaseClass):

    def __init__(self):
        super(PortGroup, self).__init__()
        self.name = None
        self.vlanId = 0
        self.numPorts = 0

    def setName(self, name):
        self.name = name

    def setVlanId(self, vlan_id):
        self.vlanId = vlan_id

    def setNumPorts(self, num_ports):
        self.numPorts = num_ports


class Vm(VCenterBaseClass):

    def __init__(self):
        super(Vm, self).__init__()
        self.name = None
        self.hypervisorName = None
        self.virtualNics = []

    def setName(self, name):
        self.name = name

    def setHypervisorName(self, hv_name):
        self.hypervisorName = hv_name

    def addVnic(self, vnic):
        self.virtualNics.append(vnic)


class Vnic(VCenterBaseClass):

    def __init__(self):
        super(Vnic, self).__init__()
        self.macAddress = None
        self.network = None

    def setMacAddress(self, mac_address):
        self.macAddress = mac_address

    def setNetwork(self, network):
        self.network = network


'''
This class implements logic for collecting data from vCenter. It uses vCenter management API (pyVmomi)
'''


class VCenterClient(object):

    def __init__(self, host, user, password, logger):
        try:
            self.host = host
            ssl_ctx = ssl.SSLContext(ssl.PROTOCOL_SSLv23)
            ssl_ctx.verify_mode = ssl.CERT_NONE
            self.connection = VCenterAPI.VCENTER_CLASS_CONNECT(
                host=self.host, user=user, pwd=password, port=443, sslContext=ssl_ctx)
            atexit.register(
                VCenterAPI.VCENTER_CLASS_DISCONNECT,
                self.connection)
            self.logger = logger
        except Exception as e:
            raise CandidDataCollectionException(
                'Failed to connect to vCenter: %s' % str(e))

    def close(self):
        try:
            VCenterAPI.VCENTER_CLASS_DISCONNECT(self.connection)
        except Exception as e:
            self.logger.warning(
                'Failed to close vCenter client: {}'.format(
                    str(e)))

    '''
    Multiplexer for handling queries based on query id
    '''

    def runQuery(self, query_id, cmd):
        self.logger.debug(
            'Running query: id = {}, cmd = {}'.format(
                query_id, cmd))
        if query_id == QueryId.VCENTER_VCENTER:
            return self.getVCenter().toJSON()
        else:
            self.logger.warning('Unsupported query: id = {}'.format(query_id))
            return None

    '''
    Get VCenter instance in vCenter object model
    '''

    def getVCenter(self):
        dc_view = None
        try:
            # vCenter
            vcenter = VCenter()
            vcenter.setHost(self.host)
            vcenter.setVersion('5.5')

            # Datacenters
            content = self.connection.RetrieveContent()
            dc_view = content.viewManager.CreateContainerView(
                content.rootFolder, [VCenterAPI.VCENTER_MODULE_VIM.Datacenter], True)
            for dc in dc_view.view:
                datacenter = self.getDatacenter(dc, content)
                vcenter.addDatacenter(datacenter)

            return vcenter
        except Exception as e:
            raise CandidDataCollectionException(str(e))
        finally:
            if dc_view:
                dc_view.Destroy()

    '''
    Get Datacenter instance for a given datacenter(dc) in vCenter object model
    '''

    def getDatacenter(self, dc, content):
        host_view = None
        dvs_view = None
        vm_view = None
        try:
            datacenter = Datacenter()
            datacenter.setName(dc.name)

            # Hypervisors
            host_view = content.viewManager.CreateContainerView(
                dc, [VCenterAPI.VCENTER_MODULE_VIM.HostSystem], True)
            for host in host_view.view:
                hypervisor = self.getHypervisor(host)
                datacenter.addHypervisor(hypervisor)

            # DVS
            dvs_view = content.viewManager.CreateContainerView(
                dc, [VCenterAPI.VCENTER_MODULE_VIM.DistributedVirtualSwitch], True)
            for dvs in dvs_view.view:
                dvswtch = self.getDvs(dvs)
                datacenter.addDvs(dvswtch)

            # Virtual machines
            vm_view = content.viewManager.CreateContainerView(
                dc, [VCenterAPI.VCENTER_MODULE_VIM.VirtualMachine], True)
            for vm in vm_view.view:
                vrtmx = self.getVm(vm, content)
                datacenter.addVm(vrtmx)

            return datacenter
        except Exception as e:
            raise CandidDataCollectionException(str(e))
        finally:
            if host_view:
                host_view.Destroy()
            if dvs_view:
                dvs_view.Destroy()
            if vm_view:
                vm_view.Destroy()

    '''
    Get Hypervisor instance for a given host in vCenter object model
    '''

    def getHypervisor(self, host):
        try:
            hypvsr = Hypervisor()
            hypvsr.setName(host.name)

            # Physical Nics
            for pnic in host.config.network.pnic:
                phynic = self.getPhysicalNic(pnic)
                hypvsr.addPhysicalNic(phynic)

            dnsConfig = HypervisorDnsConfig()
            dnsConfig.setHostName(host.config.network.dnsConfig.hostName)
            dnsConfig.setDomainName(host.config.network.dnsConfig.domainName)
            network = HypervisorNetwork()
            network.setDnsConfig(dnsConfig)
            hypvsr.setNetwork(network)

            return hypvsr
        except Exception as e:
            raise CandidDataCollectionException(str(e))

    '''
    Get PhysicalNic instance for a given physical NIC(pnic) in vCenter object model
    '''

    def getPhysicalNic(self, pnic):
        try:
            phynic = PhysicalNic()
            phynic.setDeviceName(pnic.device)
            phynic.setMacAddress(pnic.mac)
            phynic.setIpAddress(pnic.spec.ip.ipAddress)
            return phynic
        except Exception as e:
            raise CandidDataCollectionException(str(e))

    '''
    Get Dvs instance for a given distributed virtual switch(dvs) in vCenter object model
    '''

    def getDvs(self, dvs):
        try:
            dvswtch = Dvs()
            dvswtch.setName(dvs.name)
            dvswtch.setLdp(dvs.config.linkDiscoveryProtocolConfig.protocol)

            # Port groups
            for dvpg in dvs.portgroup:
                prtgrp = self.getPortGroup(dvpg)
                dvswtch.addPortGroup(prtgrp)

            return dvswtch
        except Exception as e:
            raise CandidDataCollectionException(str(e))

    '''
    Get PortGroup instance for a given distributed port group(dvpg) in vCenter object model
    '''

    def getPortGroup(self, dvpg):
        try:
            prtgrp = PortGroup()
            prtgrp.setName(dvpg.name)
            prtgrp.setVlanId(self.getVlanId(dvpg))
            prtgrp.setNumPorts(dvpg.config.numPorts)
            return prtgrp
        except Exception as e:
            raise CandidDataCollectionException(str(e))

    '''
    Get VlanId of a given distributed port group(dvpg) in vCenter object model
    '''

    def getVlanId(self, dvpg):
        vlan_id = 0
        vlan = dvpg.config.defaultPortConfig.vlan
        # Up-link port group has a port range, which we may need to handle
        # differently
        if isinstance(
                vlan,
                VCenterAPI.VCENTER_MODULE_VIM.dvs.VmwareDistributedVirtualSwitch.VlanIdSpec):  # Not up-link
            vlan_id = vlan.vlanId
        return vlan_id

    '''
    Get Vm instance for a given virtual machine(vm) in vCenter object model
    '''

    def getVm(self, vm, content):
        try:
            vrtmx = Vm()
            vrtmx.setName(vm.name)
            if vm.runtime.host:
                vrtmx.setHypervisorName(vm.runtime.host.name)

            # Vnics
            for dev in vm.config.hardware.device:
                if isinstance(
                        dev,
                        VCenterAPI.VCENTER_MODULE_VIM.vm.device.VirtualEthernetCard):
                    vrtnic = self.getVnic(dev, content)
                    vrtmx.addVnic(vrtnic)

            return vrtmx
        except Exception as e:
            raise CandidDataCollectionException(str(e))

    '''
    Get Vnic instance for a given virtual ethernet card(dev) in vCenter object model
    '''

    def getVnic(self, dev, content):
        if hasattr(dev.backing, 'port'):
            port_group_key = dev.backing.port.portgroupKey
            dvs_uuid = dev.backing.port.switchUuid
            try:
                dvs = content.dvSwitchManager.QueryDvsByUuid(dvs_uuid)
                port_group = dvs.LookupDvPortGroup(port_group_key)
                network = port_group.config.name
            except BaseException:
                network = None
        else:
            network = dev.backing.network.name

        vrtnic = Vnic()
        vrtnic.setMacAddress(dev.macAddress)
        vrtnic.setNetwork(network)

        return vrtnic


'''
This is the top-level API for F5 data collection
'''


class F5API(ThirdPartyAPIBase):

    DEFAULT_QUERY_TIMEOUT = 60  # sec
    DEFAULT_SESSION_TIMEOUT = 120  # sec
    SUPPORTED_F5_VERSIONS = ['12.1.2', '12.1.3.5']
    SUPPORTED_F5_SDK_VERSION = ['3.0.21']

    @staticmethod
    def parseArguments(arg_dic, svc_ctx):
        try:
            svc_dic = ThirdPartyAPIBase.parseArguments(arg_dic, svc_ctx)
            svc_dic.update({'desc': 'F5'})
        except KeyError as e:
            raise CandidDataCollectionException(
                'Malformed third-party service arguments: {}'.format(str(e)))

    @staticmethod
    def getTopoNode(svc_dic):
        node = ThirdPartyAPIBase.getTopoNode(svc_dic)
        node.node_id = SyntheticNodeIdProvider.getNodeId(
            Vendor.F5.value, Product.LOADBALANCER.value, svc_dic['id'])
        node.node_name = svc_dic['entityName']
        if 'chassisId' in svc_dic:
            node.node_dn = 'f5/{}/{}'.format(svc_dic['entityName'], svc_dic['chassisId'])
        else:
            node.node_dn = 'f5/{}'.format(svc_dic['entityName'])
        node.node_role = 'f5'
        if svc_dic['public_ip']:
            node.node_public_ip = svc_dic['public_ip']
        return node

    @staticmethod
    def checkSanity(svc_dic):
        ThirdPartyAPIBase.checkSanity(svc_dic)
        svc_dic.update({'is_login': F5API.checkServiceLogin(svc_dic)})
        svc_dic.update({'is_supported': F5API.checkServiceSupport(svc_dic)})

    @staticmethod
    def checkServiceLogin(svc_dic):
        try:
            if F5_ACCESS == 'rest':
                if svc_dic['public_ip']:
                    host = svc_dic['public_ip']
                else:
                    host = svc_dic['host']
                url = 'https://{}:{}/mgmt/tm/ltm'.format(host, 443)
                session = F5Session(url, svc_dic['user'], svc_dic['password'],
                                    timeout=F5API.DEFAULT_QUERY_TIMEOUT,
                                    request_format='json')
                rest_access = F5RestAccess(session)
                code, response = rest_access.getRawResponse(url)
                rest_access.logout()
                if(code != 200):
                    login = False
                    print("F5 client creation host :%s user:%s pass:%s success code:%s response:%s" %
                      (url, svc_dic['user'], svc_dic['password'], code, response))
                else:
                    login = True
            else:
                client = F5Client( svc_dic['host'], svc_dic['user'], svc_dic['password'], None)
                del client
                login = True
        except BaseException:
            print("Create F5 client creation host :%s user:%s pass:%s failed" %
                  (url, svc_dic['user'], svc_dic['password']))
            login = False
        return login

    @staticmethod
    def checkModuleVersion():
        if F5_ACCESS == 'rest':
            valid = True
            return 'f5-rest', F5API.SUPPORTED_F5_SDK_VERSION, valid
        try:
            import pkg_resources
            valid = pkg_resources.get_distribution(
                'f5-sdk').version == F5API.SUPPORTED_F5_SDK_VERSION
        except BaseException:
            valid = False
        return 'f5-sdk', F5API.SUPPORTED_F5_SDK_VERSION, valid


    @staticmethod
    def checkServiceSupport(svc_dic):
        if F5_ACCESS == 'rest':
            return True
        try:
            client = F5Client( svc_dic['host'], svc_dic['user'], svc_dic['password'], None)
            supported = client.getApplianceVersion() in F5API.SUPPORTED_F5_VERSIONS
            del client
        except BaseException:
            print("Create F5 client creation host :%s user:%s pass:%s version failed" %
                  (svc_dic['host'], svc_dic['user'], svc_dic['password']))
            supported = False
        return supported

    @classmethod
    def loadModules(cls):
        if F5_ACCESS == 'rest':
            return
        try:
            cls.F5_CLASS_EXCEPTION = F5API.loadClass(
                'f5.sdk_exception', 'F5SDKError')
            cls.F5_MANAGEMENT_ROOT = F5API.loadClass(
                'f5.bigip', 'ManagementRoot')
        except ImportError as e:
            raise CandidDataCollectionException(
                "Error while importing third-party modules. {}".format(str(e)))

    @staticmethod
    def loadClass(module_name, clazz_name):
        try:
            module = importlib.import_module(module_name)
            return getattr(module, clazz_name)
        except BaseException:
            raise

'''
This class implements logic for collecting data from F5. It uses F5 SDK.
'''

class F5Client(object):

    def __init__(self, host, user, password, logger, timeout=F5API.DEFAULT_SESSION_TIMEOUT):
        try:
            self.logger = logger
            if self.logger:
                self.logger.info("Create F5 client creation host :%s user:%s pass:%s" % (host, user, password))
            self.session = F5API.F5_MANAGEMENT_ROOT(host, user, password)
        except F5API.F5_CLASS_EXCEPTION as e:
            msg = 'Code={}, Message={}'.format(e.errorcode, e.message)
            raise CandidDataCollectionException(
                'Failed to create session F5 Error: {}'.format(msg))
        except Exception as e:
            msg = 'Message={}'.format(e.args)
            raise CandidDataCollectionException(
                'Failed to create session: {}'.format(msg))

    def close(self):
        del self.session
        return

    '''
    Get version number of remote appliance
    '''

    def getApplianceVersion(self):
        version = 'unresolved'
        try:
            versions = self.session.tm.sys.version.load()
            entries = versions.attrs.get('entries')
            version = entries['https://localhost/mgmt/tm/sys/version/0']['nestedStats']['entries']['Version']['description']
        except BaseException:
            pass
        return version

    '''
    Multiplexer for handling queries based on query id
    '''

    def runQuery(self, query_id, cmd):
        try:
            self.logger.info(
                'F5 Running query: Id={}, Cmd={}'.format(
                    query_id, cmd))
            result = None
            if query_id == QueryId.F5_SYSTEM:
                result = self.getSystem()
            elif query_id == QueryId.F5_NETWORK:
                result = self.getNetwork()
            elif query_id == QueryId.F5_ARP:
                result = self.getARP()
            elif query_id == QueryId.F5_POOL:
                result = self.getPool()
            elif query_id == QueryId.F5_VLAN:
                result = self.getVLAN()
            else:
                self.logger.warning('Unsupported query: Id={}'.format(query_id))
            self.logger.info('Id=%s result %s' %(query_id, json.dumps(result)))
            return json.dumps(result) if result else ''
        except F5API.F5_CLASS_EXCEPTION as e:
            msg = 'Code={}, Message={}'.format(e.errorcode, e.message)
            raise CandidDataCollectionException(
                'Failed to run query: {}'.format(msg))
        except Exception as e:
            msg = 'Message={}'.format(e.args)
            raise CandidDataCollectionException(
                'Failed to run query: {}'.format(msg))

    '''
    Get F5 system information
    '''

    def getSystem(self):
        try:
            devices = self.session.tm.cm.devices.get_collection()
            items = []
            system = {}
            for device in devices:
                d = {}
                d.update(chassisId=device.chassisId)
                d.update(name=device.name)
                items.append(d)
            system.update(kind="tm.net.devices")
            system.update(items=items)
            return system
        except BaseException:
            raise

    '''
       Get F5 Network information
    '''

    def getNetwork(self):
        try:
            interfaces = self.session.tm.net.interfaces.get_collection()

            items = []
            network = {}
            for intf in interfaces:
                d = {}
                d.update(name=intf.name)
                d.update(enabled=intf.enabled)
                d.update(lldpAdmin=intf.lldpAdmin)
                d.update(mediaActive=intf.mediaActive)
                d.update(macAddress=intf.macAddress)
                items.append(d)
            network.update(items=items)
            network.update(kind="tm.net.interfaces")
            return network
        except BaseException:
            raise

    '''
       Get F5 getARP information
    '''

    def getARP(self):
        try:
            arps = self.session.tm.net.arps.get_collection()

            items = []
            arpList = {}
            for arp in arps:
                d = {}
                d.update(name=arp.name)
                items.append(d)
            arpList.update(kind="tm.net.arps")
            arpList.update(items=items)
            return arpList
        except BaseException:
            raise

    '''
       Get F5 getPool information
    '''

    def getPool(self):
        try:
            pools = self.session.tm.ltm.pools.get_collection()
            items = []
            poolList = {}
            for pool in pools:
                d = {}
                d.update(name=pool.name)
                members = pool.members_s.get_collection()
                memItems = []
                membersReference = {}
                for member in members:
                    i = {}
                    i.update(name=member.name)
                    i.update(state=member.state)
                    i.update(address=member.address)
                    memItems.append(i)

                membersReference.update(items=memItems)
                d.update(membersReference=membersReference)
                items.append(d)
            poolList.update(kind="tm.ltm.pools")
            poolList.update(items=items)
            return poolList
        except BaseException:
            raise

    '''
       Get F5 getVlan information
    '''

    def getVLAN(self):
        try:
            vlans = self.session.tm.net.vlans.get_collection()
            items = []
            vlanList = {}

            for vlan in vlans:
                d = {}
                d.update(name=vlan.name)
                d.update(tag=vlan.tag)
                d.update(learning=vlan.learning)
                intfs = vlan.interfaces_s.get_collection()
                intfItems = []
                interfacesReference = {}

                interfacesReference.update(isSubcollection=vlan.interfacesReference.get('isSubcollection'))
                for intf in intfs:
                    print(intf)
                    i = {}
                    i.update(name=intf.name)
                    i.update(fullPath=intf.fullPath)
                    i.update(tagMode=intf.tagMode)
                    i.update(tagged=getattr(intf, 'tagged', False))
                    intfItems.append(i)

                interfacesReference.update(items=intfItems)
                d.update(interfacesReference=interfacesReference)
                items.append(d)
            vlanList.update(kind="tm.net.vlans")
            vlanList.update(items=items)
            return vlanList
        except BaseException:
            raise


'''
This is the top-level API for NetScaler data collection
'''


class NetScalerAPI(ThirdPartyAPIBase):

    SUPPORTED_NETSCALER_VERSIONS = ['10.5', '11.0', '12.0']
    SUPPORTED_NITRO_VERSION = '1.0'
    DEFAULT_SESSION_TIMEOUT = 120  # sec

    @staticmethod
    def parseArguments(arg_dic, svc_ctx):
        try:
            svc_dic = ThirdPartyAPIBase.parseArguments(arg_dic, svc_ctx)
            svc_dic.update({'desc': 'NetScaler'})
        except KeyError as e:
            raise CandidDataCollectionException(
                'Malformed third-party service arguments: {}'.format(str(e)))

    @staticmethod
    def getTopoNode(svc_dic):
        node = ThirdPartyAPIBase.getTopoNode(svc_dic)
        node.node_id = SyntheticNodeIdProvider.getNodeId(
            Vendor.CITRIX_NETSCALER.value, Product.LOADBALANCER.value, svc_dic['id'])
        node.node_dn = 'topology/netscaler/node-{}'.format(node.node_id)
        node.node_role = 'netscaler'
        return node

    @staticmethod
    def checkModuleVersion():
        try:
            import pkg_resources
            valid = pkg_resources.get_distribution(
                'nitro-python').version == NetScalerAPI.SUPPORTED_NITRO_VERSION
        except BaseException:
            valid = False
        return 'nitro-python', NetScalerAPI.SUPPORTED_NITRO_VERSION, valid

    @classmethod
    def loadModules(cls):
        try:
            cls.NETSCALER_CLASS_EXCEPTION = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.exception.nitro_exception', 'nitro_exception')
            cls.NETSCALER_CLASS_JSON = staticmethod(NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.base.Json', 'Json'))
            cls.NETSCALER_CLASS_SESSION = staticmethod(NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.service.nitro_service', 'nitro_service'))
            cls.NETSCALER_CLASS_SERVER = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.basic.server', 'server')
            cls.NETSCALER_CLASS_SERVERBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.basic.server_binding',
                'server_binding')
            cls.NETSCALER_CLASS_SERVICE = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.basic.service', 'service')
            cls.NETSCALER_CLASS_SERVICEBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.basic.service_binding',
                'service_binding')
            cls.NETSCALER_CLASS_SERVICEGROUP = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.basic.servicegroup', 'servicegroup')
            cls.NETSCALER_CLASS_SERVICEGROUPBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.basic.servicegroup_binding',
                'servicegroup_binding')
            cls.NETSCALER_CLASS_VERSION = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nsversion', 'nsversion')
            cls.NETSCALER_CLASS_IP = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nsip', 'nsip')
            cls.NETSCALER_CLASS_IP6 = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nsip6', 'nsip6')
            cls.NETSCALER_CLASS_TRAFFICDOMAIN = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nstrafficdomain',
                'nstrafficdomain')
            cls.NETSCALER_CLASS_TRAFFICDOMAINBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nstrafficdomain_binding',
                'nstrafficdomain_binding')
            cls.NETSCALER_CLASS_ACL = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nsacl', 'nsacl')
            cls.NETSCALER_CLASS_ACL6 = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nsacl6', 'nsacl6')
            cls.NETSCALER_CLASS_SIMPLEACL = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nssimpleacl', 'nssimpleacl')
            cls.NETSCALER_CLASS_SIMPLEACL6 = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nssimpleacl6', 'nssimpleacl6')
            cls.NETSCALER_CLASS_PBR = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nspbr', 'nspbr')
            cls.NETSCALER_CLASS_PBR6 = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.ns.nspbr6', 'nspbr6')
            cls.NETSCALER_CLASS_LLDPNEIGHBORS = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.lldp.lldpneighbors',
                'lldpneighbors')
            cls.NETSCALER_CLASS_LLDPPARAM = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.lldp.lldpparam', 'lldpparam')
            cls.NETSCALER_CLASS_INTERFACE = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.Interface', 'Interface')
            cls.NETSCALER_CLASS_CHANNEL = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.channel', 'channel')
            cls.NETSCALER_CLASS_CHANNELBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.channel_binding',
                'channel_binding')
            cls.NETSCALER_CLASS_IPTUNNEL = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.iptunnel', 'iptunnel')
            cls.NETSCALER_CLASS_VLAN = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.vlan', 'vlan')
            cls.NETSCALER_CLASS_VLANBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.vlan_binding',
                'vlan_binding')
            cls.NETSCALER_CLASS_VXLAN = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.vxlan', 'vxlan')
            cls.NETSCALER_CLASS_VXLANBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.vxlan_binding',
                'vxlan_binding')
            cls.NETSCALER_CLASS_BRIDGEGROUP = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.bridgegroup', 'bridgegroup')
            cls.NETSCALER_CLASS_BRIDGEGROUPBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.bridgegroup_binding',
                'bridgegroup_binding')
            cls.NETSCALER_CLASS_FORWARDINGSESSION = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.forwardingsession',
                'forwardingsession')
            cls.NETSCALER_CLASS_BRIDGETABLE = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.bridgetable', 'bridgetable')
            cls.NETSCALER_CLASS_ROUTE = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.route', 'route')
            cls.NETSCALER_CLASS_ROUTE6 = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.route6', 'route6')
            cls.NETSCALER_CLASS_IPSET = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.ipset', 'ipset')
            cls.NETSCALER_CLASS_IPSETBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.ipset_binding',
                'ipset_binding')
            cls.NETSCALER_CLASS_NETPROFILE = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.netprofile', 'netprofile')
            cls.NETSCALER_CLASS_VPATH = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.vpath', 'vpath')
            cls.NETSCALER_CLASS_VPATHPARAM = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.network.vpathparam', 'vpathparam')
            cls.NETSCALER_CLASS_LBVSERVER = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.lb.lbvserver', 'lbvserver')
            cls.NETSCALER_CLASS_LBVSERVERBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.lb.lbvserver_binding',
                'lbvserver_binding')
            cls.NETSCALER_CLASS_LBMONITOR = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.lb.lbmonitor', 'lbmonitor')
            cls.NETSCALER_CLASS_LBMONITORBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.lb.lbmonitor_binding',
                'lbmonitor_binding')
            cls.NETSCALER_CLASS_LBGROUP = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.lb.lbgroup', 'lbgroup')
            cls.NETSCALER_CLASS_LBGROUPBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.lb.lbgroup_binding',
                'lbgroup_binding')
            cls.NETSCALER_CLASS_GSLBVSERVER = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.gslb.gslbvserver', 'gslbvserver')
            cls.NETSCALER_CLASS_GSLBVSERVERBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.gslb.gslbvserver_binding',
                'gslbvserver_binding')
            cls.NETSCALER_CLASS_GSLBSERVICE = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.gslb.gslbservice', 'gslbservice')
            cls.NETSCALER_CLASS_GSLBSITE = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.gslb.gslbsite', 'gslbsite')
            cls.NETSCALER_CLASS_GSLBSITEBINDING = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.gslb.gslbsite_binding',
                'gslbsite_binding')
            cls.NETSCALER_CLASS_GSLBDOMAIN = NetScalerAPI.loadClass(
                'nssrc.com.citrix.netscaler.nitro.resource.config.gslb.gslbdomain', 'gslbdomain')
        except ImportError as e:
            raise CandidDataCollectionException(
                "Error while importing third-party modules. {}".format(str(e)))

    @staticmethod
    def loadClass(module_name, clazz_name):
        try:
            module = importlib.import_module(module_name)
            return getattr(module, clazz_name)
        except BaseException:
            raise

    @staticmethod
    def checkSanity(svc_dic):
        ThirdPartyAPIBase.checkSanity(svc_dic)
        svc_dic.update({'is_login': NetScalerAPI.checkServiceLogin(svc_dic)})
        svc_dic.update(
            {'is_supported': NetScalerAPI.checkServiceSupport(svc_dic)})

    @staticmethod
    def checkServiceLogin(svc_dic):
        try:
            client = NetScalerClient(
                svc_dic['host'],
                svc_dic['user'],
                svc_dic['password'],
                None)
            client.close()
            login = True
        except BaseException:
            login = False
        return login

    @staticmethod
    def checkServiceSupport(svc_dic):
        client = None
        try:
            client = NetScalerClient(
                svc_dic['host'],
                svc_dic['user'],
                svc_dic['password'],
                None)
            supported = client.getApplianceVersion() in NetScalerAPI.SUPPORTED_NETSCALER_VERSIONS
        except BaseException:
            supported = False
        finally:
            if client:
                client.close()
        return supported


'''
This class implements logic for collecting data from NetScaler. It uses NetScaler SDK.
'''


class NetScalerClient(object):

    def __init__(self, host, user, password, logger,
                 timeout=NetScalerAPI.DEFAULT_SESSION_TIMEOUT):
        try:
            self.session = NetScalerAPI.NETSCALER_CLASS_SESSION(host, "http")
            self.session.login(user, password, timeout)
            self.logger = logger
        except NetScalerAPI.NETSCALER_CLASS_EXCEPTION as e:
            msg = 'Code={}, Message={}'.format(e.errorcode, e.message)
            raise CandidDataCollectionException(
                'Failed to create session: {}'.format(msg))
        except Exception as e:
            msg = 'Message={}'.format(e.args)
            raise CandidDataCollectionException(
                'Failed to create session: {}'.format(msg))

    def close(self):
        try:
            self.session.logout()
        except NetScalerAPI.NETSCALER_CLASS_EXCEPTION as e:
            msg = 'Code={}, Message={}'.format(e.errorcode, e.message)
            self.logger.warning('Failed to close session: {}'.format(msg))
        except Exception as e:
            msg = 'Message={}'.format(e.args)
            self.logger.warning('Failed to close session: {}'.format(msg))

    '''
    Get version number of remote appliance
    '''

    def getApplianceVersion(self):
        version = 'unresolved'
        try:
            versions = NetScalerAPI.NETSCALER_CLASS_VERSION.get(self.session)
            # e.g. NetScaler NS10.5: Build 66.6.nc, Date: May 13 2017, 15:56:26
            version_1 = versions[0].version.split(':')[0]
            version = version_1[len('NetScaler NS'):] if version_1.startswith(
                'NetScaler NS') else '0.0'
        except BaseException:
            pass
        return version

    '''
    Multiplexer for handling queries based on query id
    '''

    def runQuery(self, query_id, cmd):
        try:
            self.logger.debug(
                'Running query: Id={}, Cmd={}'.format(
                    query_id, cmd))
            result = None
            if query_id == QueryId.NETSCALER_SYSTEM:
                result = self.getSystem()
            elif query_id == QueryId.NETSCALER_NETWORK:
                result = self.getNetwork()
            elif query_id == QueryId.NETSCALER_LB:
                result = self.getLB()
            elif query_id == QueryId.NETSCALER_GSLB:
                result = self.getGSLB()
            else:
                self.logger.warning('Unsupported query: Id={}'.format(query_id))
            return json.dumps(result) if result else ''
        except NetScalerAPI.NETSCALER_CLASS_EXCEPTION as e:
            msg = 'Code={}, Message={}'.format(e.errorcode, e.message)
            raise CandidDataCollectionException(
                'Failed to run query: {}'.format(msg))
        except Exception as e:
            msg = 'Message={}'.format(e.args)
            raise CandidDataCollectionException(
                'Failed to run query: {}'.format(msg))

    '''
    Get NetScaler system information
    '''

    def getSystem(self):
        try:
            features = self.session.get_enabled_features()
            modes = self.session.get_enabled_modes()
            servers = NetScalerAPI.NETSCALER_CLASS_SERVER.get(self.session)
            server_bindings = self.getBindings(
                servers,
                NetScalerAPI.NETSCALER_CLASS_SERVER,
                NetScalerAPI.NETSCALER_CLASS_SERVERBINDING)
            services = NetScalerAPI.NETSCALER_CLASS_SERVICE.get(self.session)
            service_bindings = self.getBindings(
                services,
                NetScalerAPI.NETSCALER_CLASS_SERVICE,
                NetScalerAPI.NETSCALER_CLASS_SERVICEBINDING)
            service_groups = NetScalerAPI.NETSCALER_CLASS_SERVICEGROUP.get(
                self.session)
            service_group_bindings = self.getBindings(
                service_groups,
                NetScalerAPI.NETSCALER_CLASS_SERVICEGROUP,
                NetScalerAPI.NETSCALER_CLASS_SERVICEGROUPBINDING)
            doc = {'enabled_feature': features, 'enabled_mode': modes}
            doclets = [servers, server_bindings, services, service_bindings,
                       service_groups, service_group_bindings]
            doc = self.concatJsonDoclets(doc, doclets)
            return doc
        except BaseException:
            raise

    '''
    Get network information
    '''

    def getNetwork(self):
        try:
            ips = NetScalerAPI.NETSCALER_CLASS_IP.get(self.session)
            ip6s = NetScalerAPI.NETSCALER_CLASS_IP6.get(self.session)
            traffic_doms = NetScalerAPI.NETSCALER_CLASS_TRAFFICDOMAIN.get(
                self.session)
            traffic_dom_bindings = self.getBindings(
                traffic_doms,
                NetScalerAPI.NETSCALER_CLASS_TRAFFICDOMAIN,
                NetScalerAPI.NETSCALER_CLASS_TRAFFICDOMAINBINDING)
            acls = NetScalerAPI.NETSCALER_CLASS_ACL.get(self.session)
            acl6s = NetScalerAPI.NETSCALER_CLASS_ACL6.get(self.session)
            simple_acls = NetScalerAPI.NETSCALER_CLASS_SIMPLEACL.get(
                self.session)
            simple_acl6s = NetScalerAPI.NETSCALER_CLASS_SIMPLEACL6.get(
                self.session)
            pbrs = NetScalerAPI.NETSCALER_CLASS_PBR.get(self.session)
            pbr6s = NetScalerAPI.NETSCALER_CLASS_PBR6.get(self.session)
            lldp_neighbors = NetScalerAPI.NETSCALER_CLASS_LLDPNEIGHBORS.get(
                self.session)
            lldp_params = NetScalerAPI.NETSCALER_CLASS_LLDPPARAM.get(
                self.session)
            interfaces = NetScalerAPI.NETSCALER_CLASS_INTERFACE.get(
                self.session)
            channels = NetScalerAPI.NETSCALER_CLASS_CHANNEL.get(self.session)
            channel_bindings = self.getBindings(
                channels,
                NetScalerAPI.NETSCALER_CLASS_CHANNEL,
                NetScalerAPI.NETSCALER_CLASS_CHANNELBINDING)
            ip_tunnels = NetScalerAPI.NETSCALER_CLASS_IPTUNNEL.get(
                self.session)
            vlans = NetScalerAPI.NETSCALER_CLASS_VLAN.get(self.session)
            vlan_bindings = self.getBindings(
                vlans,
                NetScalerAPI.NETSCALER_CLASS_VLAN,
                NetScalerAPI.NETSCALER_CLASS_VLANBINDING)
            vxlans = NetScalerAPI.NETSCALER_CLASS_VXLAN.get(self.session)
            vxlan_bindings = self.getBindings(
                vxlans,
                NetScalerAPI.NETSCALER_CLASS_VXLAN,
                NetScalerAPI.NETSCALER_CLASS_VXLANBINDING)
            bridge_groups = NetScalerAPI.NETSCALER_CLASS_BRIDGEGROUP.get(
                self.session)
            bridge_group_bindings = self.getBindings(
                bridge_groups,
                NetScalerAPI.NETSCALER_CLASS_BRIDGEGROUP,
                NetScalerAPI.NETSCALER_CLASS_BRIDGEGROUPBINDING)
            fwd_sessions = NetScalerAPI.NETSCALER_CLASS_FORWARDINGSESSION.get(
                self.session)
            bridge_tables = NetScalerAPI.NETSCALER_CLASS_BRIDGETABLE.get(
                self.session)
            routes = NetScalerAPI.NETSCALER_CLASS_ROUTE.get(self.session)
            route6s = NetScalerAPI.NETSCALER_CLASS_ROUTE6.get(self.session)
            ip_sets = NetScalerAPI.NETSCALER_CLASS_IPSET.get(self.session)
            ip_set_bindings = self.getBindings(
                ip_sets,
                NetScalerAPI.NETSCALER_CLASS_IPSET,
                NetScalerAPI.NETSCALER_CLASS_IPSETBINDING)
            net_profiles = NetScalerAPI.NETSCALER_CLASS_NETPROFILE.get(
                self.session)
            #vpaths = NetScalerAPI.NETSCALER_CLASS_VPATH.get(self.session)
            #vpath_params = NetScalerAPI.NETSCALER_CLASS_VPATHPARAM.get(self.session)
            vpaths = ''
            vpath_params = ''
            doc = None
            doclets = [
                ips,
                ip6s,
                traffic_doms,
                traffic_dom_bindings,
                acls,
                acl6s,
                simple_acls,
                simple_acl6s,
                pbrs,
                pbr6s,
                lldp_neighbors,
                lldp_params,
                interfaces,
                channels,
                channel_bindings,
                ip_tunnels,
                vlans,
                vlan_bindings,
                vxlans,
                vxlan_bindings,
                bridge_groups,
                bridge_group_bindings,
                fwd_sessions,
                bridge_tables,
                routes,
                route6s,
                ip_sets,
                ip_set_bindings,
                net_profiles,
                vpaths,
                vpath_params]
            doc = self.concatJsonDoclets(doc, doclets)
            return doc
        except BaseException:
            raise

    '''
    Get load balancer information
    '''

    def getLB(self):
        try:
            lbvservers = NetScalerAPI.NETSCALER_CLASS_LBVSERVER.get(
                self.session)
            lbvserver_bindings = self.getBindings(
                lbvservers,
                NetScalerAPI.NETSCALER_CLASS_LBVSERVER,
                NetScalerAPI.NETSCALER_CLASS_LBVSERVERBINDING)
            lbmonitors = NetScalerAPI.NETSCALER_CLASS_LBMONITOR.get(
                self.session)
            lbmonitor_bindings = self.getBindings(
                lbmonitors,
                NetScalerAPI.NETSCALER_CLASS_LBMONITOR,
                NetScalerAPI.NETSCALER_CLASS_LBMONITORBINDING)
            lbgroups = NetScalerAPI.NETSCALER_CLASS_LBGROUP.get(self.session)
            lbgroup_bindings = self.getBindings(
                lbgroups,
                NetScalerAPI.NETSCALER_CLASS_LBGROUP,
                NetScalerAPI.NETSCALER_CLASS_LBGROUPBINDING)
            doc = None
            doclets = [lbvservers, lbvserver_bindings,
                       lbmonitors, lbmonitor_bindings,
                       lbgroups, lbgroup_bindings]
            doc = self.concatJsonDoclets(doc, doclets)
            return doc
        except BaseException:
            raise

    '''
    Get global server load balancer information
    '''

    def getGSLB(self):
        try:
            gslbvservers = NetScalerAPI.NETSCALER_CLASS_GSLBVSERVER.get(
                self.session)
            gslbvserver_bindings = self.getBindings(
                gslbvservers,
                NetScalerAPI.NETSCALER_CLASS_GSLBVSERVER,
                NetScalerAPI.NETSCALER_CLASS_GSLBVSERVERBINDING)
            gslbservices = NetScalerAPI.NETSCALER_CLASS_GSLBSERVICE.get(
                self.session)
            gslbsites = NetScalerAPI.NETSCALER_CLASS_GSLBSITE.get(self.session)
            gslbsite_bindings = self.getBindings(
                gslbsites,
                NetScalerAPI.NETSCALER_CLASS_GSLBSITE,
                NetScalerAPI.NETSCALER_CLASS_GSLBSITEBINDING)
            gslbdomains = NetScalerAPI.NETSCALER_CLASS_GSLBDOMAIN.get(
                self.session)
            doc = None
            doclets = [gslbvservers, gslbvserver_bindings, gslbservices,
                       gslbsites, gslbsite_bindings, gslbdomains]
            doc = self.concatJsonDoclets(doc, doclets)
            return doc
        except BaseException:
            raise

    '''
    Get resource key
    '''

    def getKey(self, resource):
        if isinstance(
            resource,
            (NetScalerAPI.NETSCALER_CLASS_SERVER,
             NetScalerAPI.NETSCALER_CLASS_SERVICE,
             NetScalerAPI.NETSCALER_CLASS_LBVSERVER,
             NetScalerAPI.NETSCALER_CLASS_LBGROUP,
             NetScalerAPI.NETSCALER_CLASS_GSLBVSERVER)):
            return resource.name
        if isinstance(resource, NetScalerAPI.NETSCALER_CLASS_SERVICEGROUP):
            return resource.servicegroupname
        if isinstance(
            resource,
            (NetScalerAPI.NETSCALER_CLASS_VLAN,
             NetScalerAPI.NETSCALER_CLASS_VXLAN)):
            return resource.id
        if isinstance(resource, NetScalerAPI.NETSCALER_CLASS_LBMONITOR):
            return resource.monitorname
        if isinstance(resource, NetScalerAPI.NETSCALER_CLASS_GSLBSITE):
            return resource.sitename
        if isinstance(resource, NetScalerAPI.NETSCALER_CLASS_TRAFFICDOMAIN):
            return resource.td
        raise CandidDataCollectionException(
            'Key unknown for resource type: {}'.format(
                resource.__class__.__name__))

    '''
    Get resource bindings
    '''

    def getBindings(self, resources, res_clazz, bnd_clazz):
        if res_clazz.count(self.session) == 0 or resources is None:
            return None
        res_bindings = []
        for resource in resources:
            key = self.getKey(resource)
            bindings = bnd_clazz.get(self.session, key)
            if not bindings:
                continue
            res_bindings.append(bindings)
        return res_bindings

    '''
    Concatenate JSON document elements
    '''

    def concatJsonDoclets(self, doc, doclets):
        json_serializer = NetScalerAPI.NETSCALER_CLASS_JSON()
        for doclet in doclets:
            if not doclet:
                continue
            doclet_json = json.loads(
                json_serializer.resource_to_string_bulk(doclet))
            if not doc:
                doc = doclet_json
            else:
                doc.update(doclet_json)
        return doc


'''
This class includes private data belongs to a service api instance
'''


class ThirdPartyServiceContext(object):

    def __init__(self):
        self.service_registry = []

    def getServiceRegistry(self):
        return self.service_registry

    def registerService(self, svc_dic):
        svc_dic.update({'id': len(self.service_registry)})
        self.service_registry.append(svc_dic)

    def getServiceDictionary(self, host):
        dic = {}
        for svc_dic in self.service_registry:
            public_ip = ThirdPartyServicesAPI.nat_private_to_public_translation(svc_dic['host'])
            private_ip = ThirdPartyServicesAPI.nat_public_to_private_translation(public_ip)
            svc_dic['host'] = private_ip
            svc_dic['public_ip'] = public_ip
            if public_ip == host:
                dic = svc_dic
                break
        return dic


'''
This is the top-level API for all 3rd-party data sources
'''
class SyntheticNodeIdProvider:
    # moved from below
    # On ACI side node id is unsigned 32-bit. So for 3rd-party service nodes
    SYNTHETIC_BASE_NODE_ID = 0xffffffff
    SYNTHETIC_BASE_ECO_SYSTEM_ID = 0x000000FF
    # we use max(unsigned 32-bit) + 1 and beyond
    @staticmethod
    def getNodeId(vendor, product, counter):
        # Node Id = Base (32 bits) + Vendor (8 bits) + Product (8 bits) +
        # Counter (16 bits)
        if Vendor.CISCO_NAE.value == vendor :
           id = (SyntheticNodeIdProvider.SYNTHETIC_BASE_NODE_ID << 8) | vendor
        else:
           id = (SyntheticNodeIdProvider.SYNTHETIC_BASE_ECO_SYSTEM_ID << 8) | vendor
        id = (id << 8) | product
        id = (id << 16) | counter
        return id


class ThirdPartySerivcesExplorer(object):
    def __init__(self):
        self.node_list = []
        self.svc_ctx = None

    def createSvcCtx(self, tps_list):
        configs = ''
        if tps_list:
            configs = ThirdPartyServicesAPI.convertListToConfigs(tps_list)
        self.svc_ctx = ThirdPartyServicesAPI.initialize(configs)

    def process(self):
        self.node_list = ThirdPartyServicesAPI.exploreTopology(self.svc_ctx)

    def getTopoNodeList(self):
        return self.node_list

    def getNodeInfo(self, node):
        node_ip = ThirdPartyServicesAPI.getNodeIp(node)
        svc_dic = self.svc_ctx.getServiceDictionary(node_ip)
        return svc_dic


class ThirdPartyServicesAPI(object):

    API_REGISTRY = {
        'vcenter': VCenterAPI,
        'netscaler': NetScalerAPI,
        'f5': F5API}

    @staticmethod
    def getAPI(type):
        try:
            api = ThirdPartyServicesAPI.API_REGISTRY[type]
        except KeyError:
            api = None
        return api

    @staticmethod
    def readServiceConfig(cfg_file):
        if not cfg_file:
            return
        try:
            # Parsing and serializing ensures that file contains a valid JSON.
            doc = json.load(open(cfg_file, 'r'))
            return json.dumps(doc)
        except Exception as e:
            raise CandidDataCollectionException(
                'Error while reading service configuration: {}'.format(str(e)))

    @staticmethod
    def initialize(svc_config):
        if not svc_config:
            return None
        svc_ctx = ThirdPartyServiceContext()
        try:
            svc_config = json.loads(svc_config)
            if not isinstance(svc_config, list):
                svc_config = [ svc_config ]
            for svc_args in svc_config:
                ThirdPartyServicesAPI.initializeAPI(svc_args, svc_ctx)
        except ValueError as e:
            raise CandidDataCollectionException(
                'Malformed third-party service arguments: {}'.format(str(e)))
        return svc_ctx

    @staticmethod
    # nat translation from public_ip to node_ip
    def nat_public_to_private_translation(node_ip):
        if global_nat_box and global_nat_box.nat_configuration_list:
            return global_nat_box.get_public_to_private_translation(node_ip)[0]
        return node_ip

    @staticmethod
    def nat_private_to_public_translation(node_ip):
        if global_nat_box and global_nat_box.nat_configuration_list:
            return global_nat_box.get_private_to_public_translation(node_ip)[0]
        return node_ip

    @staticmethod
    def getNodeIp(node):
        if node.node_public_ip:
            return node.node_public_ip
        else:
            return node.node_ip

    @staticmethod
    def initializeAPI(arg_dic, svc_ctx):
        try:
            if 'type' not in arg_dic:
                raise CandidDataCollectionException(
                    'Argument "type" not defined in third-party service arguments: {}'.format(arg_dic))
            svc_type = arg_dic['type']
            api = ThirdPartyServicesAPI.getAPI(svc_type)
            if not api:
                raise CandidDataCollectionException(
                    'Unsupported third-party service type: {}'.format(svc_type))
            api.parseArguments(arg_dic, svc_ctx)
            api.loadModules()
        except ValueError as e:
            raise CandidDataCollectionException(
                'Malformed third-party service arguments: {}'.format(str(e)))

    @staticmethod
    def convertListToConfigs(tpsList):
        if not tpsList:
            return ""
        configs = [json.dumps(x) for x in tpsList]
        return '|'.join(configs) if len(configs) != 0 else ''

    @staticmethod
    def setThirdPartyServiceContextConfiguration(collection_entity):
        if collection_entity:
            try:
                json_contents = json.loads(collection_entity)
                configs = []
                doc = json_contents['collectionEntities'][0].get('thirdPartyServiceContext', [])
                configs = ThirdPartyServicesAPI.convertListToConfigs(doc)
                thirdPartyServiceContext = ThirdPartyServicesAPI.initialize(configs)
                return thirdPartyServiceContext
            except Exception as e:
                raise e
        else:
            return None

    @staticmethod
    def exploreTopology(svc_ctx):
        if not svc_ctx:
            return []
        node_list = []
        for svc_dic in svc_ctx.getServiceRegistry():
            api = ThirdPartyServicesAPI.getAPI(svc_dic['type'])
            public_ip = ThirdPartyServicesAPI.nat_private_to_public_translation(svc_dic['host'])
            private_ip = ThirdPartyServicesAPI.nat_public_to_private_translation(public_ip)
            svc_dic['host'] = private_ip
            svc_dic['public_ip'] = public_ip
            api.checkSanity(svc_dic)
            node_list.append(api.getTopoNode(svc_dic))
        return node_list

    @staticmethod
    def checkModuleVersions(logger, svc_ctx):
        if not svc_ctx:
            return True
        version_check = True
        apis_in_use = set()
        for svc_dic in svc_ctx.getServiceRegistry():
            apis_in_use.add(svc_dic['type'])
        for api_name in apis_in_use:
            name, version, found = ThirdPartyServicesAPI.getAPI(
                api_name).checkModuleVersion()
            if not found:
                logger.warning(
                    'Please install {} version {}, refer to README.md'.format(
                        name, version))
            version_check = version_check and found
        return version_check

    @staticmethod
    def readPasswords(svc_ctx):
        if not svc_ctx:
            return
        for svc_dic in svc_ctx.getServiceRegistry():
            ThirdPartyServicesAPI.getAPI(svc_dic['type']).readPassword(svc_dic)


class ConnectionInformation:

    def __init__(self, connection_type, ip, port=443):
        self.connection_type = connection_type
        self.connection_ip = ip
        self.connection_reachable = False
        self.connection_port = port
        self.connection_rest_login = False
        self.connection_ssh_login = False
        # nat fields are none, so the toponodes
        # will not have these fields populated
        self.connection_public_ip = None
        self.connection_public_port = None

    def setRestLogin(self, login_result):
        self.connection_rest_login = login_result

    def setSshLogin(self, login_result):
        self.connection_ssh_login = login_result

    def isLoggedIn(self):
        return self.connection_rest_login and self.connection_ssh_login

    def setReachable(self, reachable):
        self.connection_reachable = reachable

    def setNatAttributes(self, ip, port=None):
        self.connection_public_ip = ip
        self.connection_public_port = port

    def __repr__(self):
        print_str = "connection_type: {0}, IP: {1}, port:{2}, public_ip: {3}, public_port: {4}, ssh login: {5}, rest login: {6}, reachable: {7}".format(
                    self.connection_type, self.connection_ip, self.connection_port, self.connection_public_ip, self.connection_public_port, self.connection_ssh_login, self.connection_rest_login, self.connection_reachable)
        return print_str


class Node:
    def __init__(self, ip, dn=None):
        self.node_ip = ip  # Ip of node to use based on connection preference (primary, secondary)
        self.node_inband_ip = '0.0.0.0'
        self.node_oob_ip = '0.0.0.0'
        if dn is None:
            self.node_dn = ''
        else:
            self.node_dn = dn
        self.node_fabric_st = ""
        self.node_id = 0
        self.node_pod_id = 0
        self.node_name = ""
        self.node_hostname = ""
        self.node_dns_look_up_hostname = ""
        self.node_role = UNSUPPORTED
        self.node_version = ""
        self.node_fcs = None
        self.node_quorum = None
        self.node_asic_name = None
        self.node_asic_type = None
        self.node_asic_model = ""
        self.node_admin_cluster_size = 0
        self.node_current_cluster_size = 0
        self.node_concrete_cluster_size = 0  # Represents InfraCont size
        self.node_is_login = False
        self.node_is_reachable = False
        self.node_is_supported = False
        self.node_is_configured = False
        self.node_fabric_name = ""
        self.node_fabric_uuid = ""
        self.node_fabricSt = ""
        self.node_model = ""
        self.node_intf_list = []
        self.node_admin_config = bytes()
        self.node_port = 443
        # NAT(public_ip) = node_ip, public_ip used as input into nat to reach
        # node_ip
        self.node_public_ip = None
        self.node_public_port = None  # ^^^^ but for port
        # array of ConnectionInformation
        self.node_connection_info = []
        self.node_time = None
        self.sa_fabric = ""
        self.enabled_features = [] # enum for features
        self.node_loopback_interface = -1

    def getNodeIp(self):
        if self.node_public_ip:
            return self.node_public_ip
        else:
            return self.node_ip

    def getNodePort(self):
        if self.node_public_port:
            return self.node_public_port
        return self.node_port

    def setNatIP(self, node_ip, nat_box):
        if nat_box and nat_box.nat_configuration_list:
            public_ip, public_port = nat_box.get_private_to_public_translation(
                node_ip)
            if public_ip != node_ip:
                self.node_public_ip = public_ip
                self.node_public_port = public_port
            else:
                self.node_public_ip = None
                self.node_public_port = None

    def getConnectionPreferenceUsed(self):
        if self.node_ip == "0.0.0.0":
            return ConnectionPreference.UNKNOWN
        elif self.node_ip == self.node_oob_ip:
            return ConnectionPreference.OOB
        elif self.node_ip == self.node_inband_ip:
            return ConnectionPreference.INBAND
        return ConnectionPreference.UNKNOWN

    def getPreferredNodeIp(self, preference):
        if preference == ConnectionPreference.OOB:
            return self.node_oob_ip
        elif preference == ConnectionPreference.INBAND:
            return self.node_inband_ip
        return "0.0.0.0"

    def isPreferenceUsed(self, preference):
        if preference == ConnectionPreference.OOB:
            return self.node_oob_ip == self.node_ip
        elif preference == ConnectionPreference.INBAND:
            return self.node_inband_ip == self.node_ip
        return False

    def addNodeConnectionInfo(self, connection_info):
        self.node_connection_info.insert(0, connection_info)

    def setTime(self, timestamp):
        self.node_time = timestamp

    def getTime(self):
        return self.node_time

    def setNodeName(self, name):
        self.node_name = name

    def getNodeName(self):
        return self.node_name

    def setNodeFcs(self, fcs):
        self.node_fcs = fcs

    def getNodeFcs(self):
        return self.node_fcs

    def setNodeAsicType(self, asic_type):
        self.node_asic_type = asic_type

    def getNodeAsicType(self):
        return self.node_asic_type

    def getNodeId(self):
        return self.node_id

    def setNodeId(self, node_id):
        self.node_id = node_id

    def getVersion(self):
        return self.node_version

    def setVersion(self, version):
        self.node_version = version

    def getNodeRole(self):
        return self.node_role

    def setNodeRole(self, node_role):
        self.node_role = node_role

    def isController(self):
        return (self.node_role == CONTROLLER)

    def isLeaf(self):
        return (self.node_role == LEAF)

    def isSpine(self):
        return (self.node_role == SPINE)

    def isDcnm(self):
        return (self.node_role == DCNM)

    def isMso(self):
        return (self.node_role == MSO)

    def isStandaloneSpine(self):
        return (self.node_role == STANDALONE_SPINE)

    def isStandaloneLeaf(self):
        return (self.node_role == STANDALONE_LEAF)

    def isVCenter(self):
        return (self.node_role == VCENTER)

    def isNetScaler(self):
        return (self.node_role == NETSCALER)

    def isCommandNode(self):
        return (self.node_role == COMMAND_NODE)

    def isF5(self):
        return (self.node_role == F5)

    def getCurrentClusterSize(self):
        return self.node_current_cluster_size

    def getConcreteClusterSize(self):
        return self.node_concrete_cluster_size

    def setQuorum(self, val):
        self.node_quorum = val

    def loginSuccessful(self):
        self.node_is_login = True

    def isLoginSuccess(self):
        return (self.node_is_login)

    def setLogin(self, login):
        self.node_is_login = login

    def reachable(self):
        self.node_is_reachable = True

    def supported(self):
        self.node_is_supported = True

    def getSaFabric(self):
        return self.sa_fabric

    def setSaFabric(self, sa_fabric):
        self.sa_fabric = sa_fabric

    def getEnabledFeatList(self):
        return self.enabled_features

    def setEnabledFeatList(self, feat_list):
        self.enabled_features = feat_list.copy()

    def getLoopbackInterface(self):
        # py3 will throw error if value is None and is compared against int
        if isinstance(self.node_loopback_interface, int):
            return self.node_loopback_interface
        else:
            return -1

    def setLoopbackInterface(self, loopback_interface):
        self.node_loopback_interface = loopback_interface

    def __repr__(self):

        print_str = "NODE: %s, IP: %s, Role: %s, ID: %s, Fabric State: %s, DN: %s, SW Version %s" % \
                    (self.node_name,
                     self.node_ip,
                     self.node_role,
                     self.node_id,
                     self.node_fabric_st,
                     str(self.node_dn),
                     str(self.node_version),
                     )
        if self.node_is_login is not None:
            print_str = print_str + ' login: %s' % self.node_is_login
        if self.node_is_reachable is not None:
            print_str = print_str + ' reachable: %s' % self.node_is_reachable
        if self.node_is_supported is not None:
            print_str = print_str + ' supported: %s' % self.node_is_supported
        if self.node_is_configured is not None:
            print_str = print_str + ' configured: %s' % self.node_is_configured
        if self.node_public_ip is not None:
            print_str = print_str + ' public_ip: %s' % self.node_public_ip
        if len(self.node_connection_info) >0:
            print_str = print_str + ' connection information: %s' % str(self.node_connection_info)
        else:
            print_str = print_str + ' *NO* connection information found '
        if self.node_oob_ip:
            print_str += ' node_oob_ip: %s'%str(self.node_oob_ip)
        if self.node_inband_ip:
            print_str += ' node_inband_ip: %s'%str(self.node_inband_ip)
        if self.node_role in [SPINE, STANDALONE_SPINE]:
            return print_str + ' Fabric card: %s' % self.node_fcs \
                + ' Model: %s' % self.node_asic_model
        elif self.node_role in [LEAF, STANDALONE_LEAF]:
            return print_str + ' Asic Type: %s' % self.node_asic_type \
                + ' Model: %s' % self.node_asic_model
        elif self.node_role == DCNM:
            return print_str + ' Asic Type: %s' % self.node_asic_type \
                + ' Model: %s' % self.node_asic_model \
                + ' Fabric Name: %s' %self.sa_fabric \
                + ' Loopback Interface: %s'%self.getLoopbackInterface()
        elif self.node_role == CONTROLLER:
            if self.node_quorum is None:
                node_quorum = "None"
            else:
                node_quorum = str(self.node_quorum)
            return print_str + ' Quorum:' + node_quorum + ' Admin Cluster size: '\
                + str(self.node_admin_cluster_size) + ' Current cluster size: ' \
                + str(self.node_current_cluster_size) + 'Concrete cluster size: ' \
                + str(self.node_concrete_cluster_size) + ' Fabric Name: ' \
                + self.node_fabric_name + ' Fabric uuid: ' + self.node_fabric_uuid
        return print_str


class Topology(object):

    def __init__(self):
        # ip : Node
        self.topo_node_list = {}
        # ip: node_dn : Node
        self.missing_node_ip_list = {}
        # ip: Node
        # only populated when there is a secondary connection preference
        # TODO: (vivek) - populate this or remove this field
        self.login_failed_node_list = {}

    def updateStandaloneTopoNode(self, node_ip, nat_box, node_id,
                                 node_type, node_name, sa_fabric):
        node = self.topo_node_list[node_ip]
        node.setNatIP(node_ip, nat_box)
        node.setNodeId(node_id)
        node.setNodeRole(node_type)
        node.setNodeName(node_name)
        node.setSaFabric(sa_fabric)

    def quickCopyNode(self, node, node_name_suffix, increment_node_id=0):
        copy_node = Node(node.node_ip, node.node_dn)
        copy_node.node_public_ip = node.node_public_ip
        copy_node.setNodeId(node.getNodeId()+increment_node_id)
        copy_node.setNodeName(node.getNodeName()+node_name_suffix)
        copy_node.setNodeRole(node.getNodeRole())
        return copy_node

    def createTopoNode(self, node_ip, node_dn=None):
        if node_ip and node_ip != "0.0.0.0":
            if node_ip not in self.topo_node_list:
                self.topo_node_list[node_ip] = Node(node_ip)
                if node_dn:
                    self.updateTopoNode(node_ip, "dn", node_dn)

    # get ip address if node exists
    # can be enhanced to add return only if apics that can be logged into (?)
    def getExistingNodeIp(self, node_dn, oob_ip, inb_ip, name):
        result = None

        # look through topo_node_list
        for each_node in list(self.topo_node_list.values()):
            if each_node.node_dn == node_dn:
                return each_node.node_ip
            elif(each_node.node_ip != "0.0.0.0" and
                        each_node.node_ip in [oob_ip, inb_ip]):
                return each_node.node_ip
            elif (name != "" and
                   name in [each_node.node_hostname, each_node.node_name]):
                return each_node.node_ip

        # look through missing_node_ip_list
        for each_node in list(self.missing_node_ip_list.get("0.0.0.0", {}).values()):
            if each_node.node_dn == node_dn:
                return "0.0.0.0"
            elif oob_ip != "0.0.0.0" and oob_ip == each_node.node_oob_ip:
                return "0.0.0.0"
            elif inb_ip != "0.0.0.0" and inb_ip == each_node.node_inband_ip:
                return "0.0.0.0"
            elif (name != "" and
                   name in [each_node.node_hostname, each_node.node_name]):
                return "0.0.0.0"
        return result

    def updateTopoNode(self, node_ip, node_attr, node_attr_value):
        # check if node is in topo_node_list or login_failed_node_list
        for node_list in [self.topo_node_list, self.login_failed_node_list]:
            if node_ip != '0.0.0.0' and node_ip in node_list:
                node = node_list[node_ip]
                node.__dict__['node_' + node_attr] = node_attr_value
                break;

    def createMissingOobNode(self, node_ip, node_dn):
        if node_ip == '0.0.0.0' and node_dn:
            if node_ip in self.missing_node_ip_list:
                self.missing_node_ip_list[node_ip][node_dn] = Node(
                    node_ip, node_dn)
            else:
                self.missing_node_ip_list[node_ip] = {}
                self.missing_node_ip_list[node_ip][node_dn] = Node(
                    node_ip, node_dn)

    def updateMissingOobNode(
            self,
            node_ip,
            node_dn,
            node_attr,
            node_attr_value):
        if node_ip == '0.0.0.0' and node_dn:
            self.missing_node_ip_list[node_ip][node_dn].__dict__[
                'node_' + node_attr] = node_attr_value

    def updateNodeVersion(self, node_dn, node_version):
        # If node has valid oob address, look through topo_node_list and login_failed_node_list
        for node_list in [self.topo_node_list, self.login_failed_node_list]:
            for each_node in list(node_list.keys()):
                node = node_list[each_node]
                if node.node_dn == node_dn:
                    self.updateTopoNode(node.node_ip, "version", node_version)
                    return

        # If the node has invalid oob address
        missing_node_list = list(self.missing_node_ip_list.values())
        for each_node_dn in missing_node_list:
            if each_node_dn == node_dn:
                self.updateMissingOobNode(
                    self, '0.0.0.0', each_node_dn, "version", node_version)
                return

'''
I/P : one of the APIC ip's in majority
O/P : Topology of leafs/spines, apics
    : union of all nodes seen by all apic
    : Topology events

1. Given input APIC Ips, do quorum detection
2. Calculate set of output ips in quorum
3. Check ACI Version supported?
4. Pick any apic in quorum :
   Discover OOB address of node
5. Make topology discovery independent of version
'''


class TopologyExplorer(object):

    def __init__(self, logger, apic_ips,
                 user, password,
                 login_time_out=6,
                 query_time_out=60,
                 node_time_out=120,
                 apic_login_time_out=6,
                 apic_query_time_out=60,
                 apic_node_time_out=120,
                 protocol='https', port='443', request_format='json',
                 version=None,
                 switch_version=None,
                 nat_box=None, app_mode=False, max_threads=16,
                 sa_topo_args=None,
                 cnae_mode=_APIC,
                 lan_username=None,
                 lan_password=None,
                 leaf_list=None,
                 loopback_interface=-1):
        self.logger = logger
        self.input_apic_ips = apic_ips
        self.user = user
        self.password = password
        self.login_time_out = login_time_out
        self.query_time_out = query_time_out
        self.node_time_out = node_time_out
        self.apic_login_time_out = apic_login_time_out
        self.apic_query_time_out = apic_query_time_out
        self.apic_node_time_out = apic_node_time_out
        self.version = version
        self.switch_version = switch_version
        self.max_threads = max_threads
        self.collector = None
        self.export_policy_name = None
        self.export_policy_format = None
        self.apic_time = None
        self.sa_topo_args = sa_topo_args
        self.cnae_mode = cnae_mode
        #TODO: change condition after MSO supported version is handled
        if (self.cnae_mode != _MSO):
            self.setSupportedVersions()
        # To store the query results from GenericCollector
        self.results_stash = QueryResultsStash()

        self.collection_stats_stash = CollectionStatsStash()

        # Dns resolve the input apic_ips, dcnm_ips, spine_ips & leaf_ips
        self.resolved_input_ips = []

        # Output topoNodeList
        # Key : node_dn  , value : TopoNode
        self.topology = Topology()
        self.logger.info("Parallel topology explorer...")
        if nat_box is not None:
            self.nat_box = nat_box
        else:
            self.nat_box = NatTranslator(logger)

        global global_nat_box
        global_nat_box = self.nat_box

        # should only be invoked through dag
        self.app_mode = app_mode

        self.connection_preference_primary = ConnectionPreference.INBAND
        self.connection_preference_secondary = ConnectionPreference.UNKNOWN

        # the following options are set when the json string specifying collection options is parsed
        self.lan_username = lan_username
        self.lan_password = lan_password
        self.leaf_list = leaf_list
        self.loopback_interface = loopback_interface

    def setSupportedVersions(self):
        def getSupportedVersions(version_type, aci_versions, standalone_versions):
            if version_type:
                return version_type;
            if self.cnae_mode == _APIC:
                return aci_versions
            elif self.cnae_mode == _STANDALONE:
                return standalone_versions
            else:
                error_message = "Unable to set version due to invalid cnae mode: %s"
                raise TopologyExplorerException(error_message%self.cnae_mode)

        self.version = getSupportedVersions(self.version,
                                            SUPPORTED_ACI_VERSIONS,
                                            SUPPORTED_DCNM_VERSIONS)
        self.switch_version = getSupportedVersions(self.switch_version,
                                                   SUPPORTED_SWITCH_VERSIONS,
                                                   SUPPORTED_NXFABRIC_SWITCH_VERSIONS)

    def setConnectionPreferencePrimary(self, connection_preference):
        new_connection = ConnectionPreference.getConnectionPreferenceType(
            connection_preference)
        if new_connection != ConnectionPreference.UNKNOWN:
            self.connection_preference_primary = new_connection
            if new_connection == self.getConnectionPreferenceSecondary():
                self.connection_preference_secondary = ConnectionPreference.UNKNOWN

    def getConnectionPreferencePrimary(self):
        return self.connection_preference_primary

    def setConnectionPreferenceSecondary(self, connection_preference):
        new_connection = ConnectionPreference.getConnectionPreferenceType(
            connection_preference)
        if new_connection != self.getConnectionPreferencePrimary():
            self.connection_preference_secondary = new_connection

    def getConnectionPreferenceSecondary(self):
        return self.connection_preference_secondary

    def getExportPolicyName(self):
        return self.export_policy_name

    def getExportPolicyFormat(self):
        return self.export_policy_format

    # re-instantiate a natTranslator with new nat_json file
    # all previous configs of nat_box are discarded
    def setCollectionEntityConfiguration(self, collection_entity):
        # also need to update ccg
        if collection_entity:
            try:
                json_contents = json.loads(collection_entity)
                first_entity = json_contents.get("collectionEntities")[0]
                entityFlags = first_entity.get("entityFlags")
                entityConfigExportPolicy = first_entity.get("entityConfigurationExportPolicy")
                if entityFlags:
                    if entityFlags.get("isNatEnabled"):
                        self.nat_box = NatTranslator(self.logger, first_entity.get("entityNatConfiguration"))
                        global global_nat_box
                        global_nat_box = self.nat_box
                    if entityFlags.get("isConfigurationExportPolicyEnabled") and entityConfigExportPolicy:
                        self.export_policy_name = entityConfigExportPolicy.get("exportPolicyName")
                        self.export_policy_format = entityConfigExportPolicy.get("exportFormat").lower()
                self.lan_username = first_entity.get("lanUsername")
                self.lan_password = first_entity.get("lanPassword")

            except Exception as e:
                self.logger.warning(
                    "Configuration options parse error, please check file: {0}".format(
                        collection_entity))
                raise e


    # updates public_ip and public_port for
    # also return ip that should be used (not always used)
    # input_apic = Is this a apic? If so, public_ip should equal node_ip
    def updateTopoNatConfiguration(self, node_ip):
        if self.nat_box.nat_configuration_list:
            translated_ip, translated_port = self.nat_box.get_private_to_public_translation(
                node_ip)
            if translated_ip != node_ip:
                self.topology.updateTopoNode(
                    node_ip, "public_ip", translated_ip)
                self.topology.updateTopoNode(
                    node_ip, "public_port", translated_port)
                return translated_ip
        return node_ip

    # nat translation from public_ip to node_ip
    def nat_public_to_private_translation(self, node_ip):
        if self.nat_box.nat_configuration_list:
            return self.nat_box.get_public_to_private_translation(node_ip)[0]
        return node_ip

    # nat translation from node_ip to public_ip
    def nat_private_to_public_translation(self, node_ip):
        if self.nat_box.nat_configuration_list:
            return self.nat_box.get_private_to_public_translation(node_ip)[0]
        return node_ip

    def getTopoNodeList(self):
        valid_nodes = list(self.topology.topo_node_list.values())
        invalid_nodes = list(self.topology.login_failed_node_list.values())
        if self.topology.missing_node_ip_list != {}:
            # go through each ip and add node to invalid_nodes
            for ip in list(self.topology.missing_node_ip_list.keys()):
                node = self.topology.missing_node_ip_list[ip]
                # this key has a dictionary of topoNodes
                if '0.0.0.0' == node.node_ip:
                    invalid_nodes.append(node)
        return valid_nodes + invalid_nodes

    def getQueryResultsFromStash(self):
        return self.results_stash.getQueryResults()

    def getApicTimeStamp(self):
        try:
            # this query would be made when the apic has node 0
            query_response = self.results_stash.lookupNodeQueries(
                                QueryId.LOGICAL_TIMESTAMP, 0)
            topInfo = ParseUtils.findAll(self, query_response, "topInfo")[0]
            timestamp = ParseUtils.getAttribute(
                              self, topInfo, "currentTime")
            self.logger.debug("APIC timestamp is {0}".format(timestamp))
            return timestamp
        except Exception as e:
            # lookup did not work
            self.logger.error("APIC timestamp was not retrieved due to: "+str(e))
        return None

    def addApicTime(self, topo_node_list):
        timestamp = self.getApicTimeStamp()
        for node in topo_node_list:
            if node.node_role == CONTROLLER:
                node.setTime(timestamp)

    def getApicTime(self):
        for node in list(self.topology.topo_node_list.values()):
            if node.getTime():
                return node.getTime()
        return None

    def getResolvedHost(self, host_name):
        try:
            resolved_host = gethostbyname(host_name) # for v4
            # resolved_host = getaddrinfo(host_name) # for ipv6 ip
        except BaseException:
            self.logger.warning("Address resolution failed for host"
                             + str(host_name))
            return "0.0.0.0"
            # return "::" # for ipv6 ip
        else:
            return resolved_host

    def getDnsLookupHostname(self, host_name):
        try:
            dns_lookup_host = gethostbyaddr(host_name)[0]
        except BaseException as e:
            self.logger.warning("Reverse DNS Lookup failed for host:"
                                + str(host_name) + " Error :" + str(e))
            return host_name
        else:
            return dns_lookup_host

    # Per APIC queries
    def getPodIdNodeId(self, ip):
        '''
        :param topSystem:
        :param apic_ip:
        :return: pod_id, node_id
        '''

        # assign a node_id to the app container's local ip
        if self.app_mode and ip == NAE_APP_LOCAL_IP:
            self.topology.updateTopoNode(ip, "pod_id", NAE_APP_LOCAL_POD_ID)
            node_id = SyntheticNodeIdProvider.getNodeId(Vendor.CISCO_NAE.value,
                                                      Product.NAE_LITE.value,
                                                      1)
            self.topology.updateTopoNode(ip, "id", int(node_id))
            return (NAE_APP_LOCAL_POD_ID, node_id)
        pod_id = None
        node_id = None
        top_system_rsp = self.results_stash.lookupNodeQueries(
            QueryId.LOGICAL_TOPSYSTEM_XML, ip, "node_ip")
        top_sys = ParseUtils.findAll(self, top_system_rsp,
                                     "topSystem")
        for each in top_sys:
            node_oob_ip = ParseUtils.getAttribute(self, each, "oobMgmtAddr")
            node_inband_ip = ParseUtils.getAttribute(self, each, "inbMgmtAddr")
            if node_oob_ip == ip or node_inband_ip == ip:
                node_id = int(ParseUtils.getAttribute(self, each, "id"))
                pod_id = int(ParseUtils.getAttribute(self, each, "podId"))

        if not pod_id and not node_id:
            raise TopologyExplorerException(
                "Cannot determine pod_id , node_id for apic", ip)

        return (pod_id, node_id)

    def getConcreteClusterSize(self, apic_ip, pod_id, node_id):

        runtime_size = None
        logical_clusters_rsp = self.results_stash.lookupNodeQueries(
            QueryId.LOGICAL_INFRACONT, apic_ip, "node_ip")
        clusters = ParseUtils.findAll(self, logical_clusters_rsp, "infraCont")

        for cluster in clusters:
            cluster_dn = ParseUtils.getAttribute(self, cluster, "dn")
            node_dn = "topology/" + "pod-" + \
                str(pod_id) + "/node-" + str(node_id) + "/"
            if node_dn in cluster_dn:
                runtime_size = int(
                    ParseUtils.getAttribute(
                        self, cluster, "size"))
                break

        return runtime_size

    def getHealthyClusterElements(self, apic_ip, pod_id, node_id):
        node_dn = "topology/pod-" + str(pod_id) + "/node-" + str(node_id) + "/"
        cluster_elements_rsp = self.results_stash.lookupNodeQueries(
            QueryId.LOGICAL_INFRAWINODE, apic_ip, "node_ip")
        cluster_elements = ParseUtils.findAll(self, cluster_elements_rsp,
                                              "infraWiNode")
        local_cluster_element = []
        for each_cluster_element in cluster_elements:
            health = ParseUtils.getAttribute(
                self, each_cluster_element, "health")
            oper_st = ParseUtils.getAttribute(
                self, each_cluster_element, "operSt")
            if node_dn in ParseUtils.getAttribute(
                    self,
                    each_cluster_element,
                    "dn") and health == "fully-fit" and oper_st == 'available':
                local_cluster_element.append(each_cluster_element)
        return local_cluster_element

    def getAdminClusterTargetSize(self, apic_ip):
        cluster_policy_rsp = self.results_stash.lookupNodeQueries(
            QueryId.LOGICAL_INFRACLUSTERPOL, apic_ip, "node_ip")
        policy = ParseUtils.findAll(
            self, cluster_policy_rsp, "infraClusterPol")
        return int(ParseUtils.getAttribute(self, policy[0], "size"))

    def updateNodeAttributes(self, node_ip, pod_id, node_id):
        fabric_node_rsp = self.results_stash.lookupNodeQueries(
            QueryId.LOGICAL_FABRICNODE_XML, node_ip, "node_ip")
        fabric_nodes = ParseUtils.findAll(self, fabric_node_rsp, "fabricNode")
        result = None
        for each_node in fabric_nodes:
            current_node_id = int(
                ParseUtils.getAttribute(
                    self, each_node, "id"))
            if current_node_id == node_id:
                result = each_node
                break
        self.topology.updateTopoNode(node_ip, "pod_id", pod_id)
        node_attrs = ["dn", "fabricSt", "id", "model", "name", "role"]
        for each_attr in node_attrs:
            each_attr_value = ParseUtils.getAttribute(self, result, each_attr)
            if each_attr == 'id':
                each_attr_value = int(each_attr_value)
            self.topology.updateTopoNode(node_ip, each_attr, each_attr_value)

    def checkLogin(self, ip):
        '''
        :param ip:
        :return:
        If there is at least one query result from this apic, login is successful
        TODO: Have login Result as one of the query results
        '''
        # if nat is not enabled, then translated_ip = each_apic
        public_ip = self.nat_private_to_public_translation(ip)
        results = [x for x in self.results_stash.getQueryResults() if x.getNode().getNodeIp(
        ) == public_ip and x.getQueryStatus() == GenericQueryResult.QueryStatus.SUCCESS]
        if results:
            return True
        else:
            return False

    def quorumFound(self):
        result = False
        for each_ip in list(self.topology.topo_node_list.keys()):
            node = self.topology.topo_node_list[each_ip]
            if node.node_quorum is True:
                result = True
                break
        return result

    def detectQuorum(self):
        for each_apic_host in self.input_apic_ips:
            pod_id = None
            node_id = None
            try:
                each_apic = self.getResolvedHost(each_apic_host)
                dns_lookedup_hostname = self.getDnsLookupHostname(each_apic_host)
                self.logger.info(
                    "Topology discovery in progress for apic :%s" %
                    (each_apic))
                # If dns resolution fails for apics , populate the topo nodes
                # and continue
                if each_apic == "0.0.0.0":
                    self.topology.createTopoNode(each_apic_host)
                    self.topology.updateTopoNode(
                        each_apic_host, "hostname", each_apic_host)
                    self.topology.updateTopoNode(
                        each_apic_host, "is_login", self.checkLogin(each_apic))
                    self.topology.updateTopoNode(
                        each_apic_host, "dns_look_up_hostname", dns_lookedup_hostname)
                    self.topology.updateTopoNode(
                        each_apic_host, "role", CONTROLLER)
                    self.topology.updateTopoNode(
                        each_apic_host, "is_configured", True)
                    self.topology.updateTopoNode(
                        each_apic_host, "is_reachable", False)
                    continue
                else:
                    self.resolved_input_ips.append(each_apic)

                public_ip = each_apic
                each_apic = self.nat_public_to_private_translation(
                    each_apic)  # if nat exists, translate public_ip to node_ip
                self.topology.createTopoNode(each_apic)
                self.topology.updateTopoNode(
                    each_apic, "hostname", each_apic_host)
                self.topology.updateTopoNode(
                    each_apic, "is_login", self.checkLogin(each_apic))
                self.topology.updateTopoNode(each_apic, "role", CONTROLLER)
                self.topology.updateTopoNode(each_apic, "is_configured", True)
                self.topology.updateTopoNode(each_apic, "dns_look_up_hostname", dns_lookedup_hostname)

                self.updateTopoNatConfiguration(
                    each_apic)  # adding nat configuration
                node_stats = self.collection_stats_stash.getCollectionStats(
                    public_ip)
                if node_stats:
                    reachable = node_stats[0].getReachable()
                    self.topology.updateTopoNode(
                        each_apic, "is_reachable", reachable)

                # Login
                if self.checkLogin(each_apic) is False:
                    self.logger.warning(
                        "Login into APIC Hostname: %sIP: %s  *FAILED*" %
                        (each_apic_host, each_apic))
                    continue

                # Get the pod_id, node_id of each_apic , given ip address of
                # APIC
                (pod_id, node_id) = self.getPodIdNodeId(each_apic)
                self.updateNodeAttributes(each_apic, pod_id, node_id)

                # Determine admin/target size of cluster
                admin_cluster_target_size = self.getAdminClusterTargetSize(
                    each_apic)

                # Determine runtime size of the cluster seen by each_apic
                try:
                    concrete_size = self.getConcreteClusterSize(
                        each_apic, pod_id, node_id)
                except Exception as e:
                    self.logger.warning(
                        "Run time size *NOT* found, Reason: " + str(e))
                    # Legacy behavior to support data sets w/o infraCont Query
                    concrete_size = admin_cluster_target_size
                # Runtime size
                local_cluster_element_size = len(
                    self.getHealthyClusterElements(
                        each_apic, pod_id, node_id))
                self.topology.updateTopoNode(
                    each_apic, "admin_cluster_size", admin_cluster_target_size)
                self.topology.updateTopoNode(
                    each_apic, "current_cluster_size", local_cluster_element_size)
                self.topology.updateTopoNode(
                    each_apic, "concrete_cluster_size", concrete_size)

                self.setControllerVersion(each_apic)

            except Exception as e:
                self.logger.error("Topology discovery failed for Reason: " +
                                  str(e) + "Line number:" + str(sys.exc_info()[2].tb_lineno))
                continue

    def detectMsoQuorum(self):
        for each_host in self.input_apic_ips:
            node_ids = set()
            try:
                each_mso = self.getResolvedHost(each_host)
                self.logger.info(
                    "Topology discovery in progress for mso :%s" %
                    (each_mso))
                # If dns resolution fails for  mso , populate the topo nodes
                # and continue
                if each_mso == "0.0.0.0":
                    self.topology.createTopoNode(each_host)
                    self.topology.updateTopoNode(
                        each_host, "hostname", each_host)
                    self.topology.updateTopoNode(
                        each_host, "dn", each_host)
                    self.topology.updateTopoNode(
                        each_host, "is_login", self.checkLogin(each_mso))
                    self.topology.updateTopoNode(
                        each_host, "role", MSO)
                    self.topology.updateTopoNode(
                        each_host, "is_configured", True)
                    self.topology.updateTopoNode(
                        each_host, "is_reachable", False)
                    continue
                else:
                    self.resolved_input_ips.append(each_mso)

                public_ip = each_mso
                each_mso = self.nat_public_to_private_translation(
                    each_mso)  # if nat exists, translate public_ip to node_ip
                self.topology.createTopoNode(each_mso)
                node_id = GlobalUtils.generateNodeId(
                    node_name=each_mso, node_ids=node_ids)
                self.topology.updateTopoNode(
                    each_mso, "id", node_id)
                self.topology.updateTopoNode(
                    each_mso, "hostname", each_host)
                self.topology.updateTopoNode(
                    each_host, "dn", each_host)
                self.topology.updateTopoNode(
                    each_mso, "is_login", self.checkLogin(each_mso))
                self.topology.updateTopoNode(each_mso, "role", MSO)
                self.topology.updateTopoNode(each_mso, "is_configured", True)

                self.updateTopoNatConfiguration(
                    each_mso)  # adding nat configuration
                node_stats = self.collection_stats_stash.getCollectionStats(
                    public_ip)
                if node_stats:
                    reachable = node_stats[0].getReachable()
                    self.topology.updateTopoNode(
                        each_mso, "is_reachable", reachable)

                #TODO: implement this function
                #self.setMsoControllerVersion(each_mso)

            except Exception as e:
                self.logger.error("Topology discovery failed for Reason: " +
                                  str(e) + "Line number:" + str(sys.exc_info()[2].tb_lineno))
                continue

    '''
    if the concrete size(infraCont)mismatch happens
    we cant determine for sure all apics that are fully fit
    In case of 3 APICs,  concrete size == always 3 , even if not all three apics are fully fit
    TODO: Pradhap needs to validate in case of 5 apics, if infraCont is always 5
    This check is to make sure infraCont is always 3 or 5 or 7
    '''

    def isConcreteSizeConsistent(self):
        concrete_size_set = set()
        for each_node in list(self.topology.topo_node_list.values()):
            if (each_node.isController() and each_node.node_is_login):
                concrete_size_set.add(each_node.node_concrete_cluster_size)
        if len(concrete_size_set) == 1:
            return True
        else:
            return False

    '''
    If an apic can be logged into, and has current_cluster_size >=
    concrete_cluster_size - 1, set quorum to true. Later in Function
    setQuorum, all apics which are in quorum with this apic
    (including both configured and discovered apics) will have quorum
    field values set to true.
    '''

    def setQuorumForConfiguredApics(self):
        for each_node in list(self.topology.topo_node_list.values()):
            concrete_cluster_size = each_node.getConcreteClusterSize()
            current_cluster_size = each_node.getCurrentClusterSize()
            if each_node.isController() and each_node.node_is_login and\
               (current_cluster_size >= concrete_cluster_size - 1):
                each_node.setQuorum(True)

    def createInbandToNodeDict(self, dcnm, sa_fabric_name):
        number_to_ip = {}
        try:
            fabric_nodes_rsp = self.results_stash.lookupNodeQueries(QueryId.NX_FABRIC_DCNM_GLOBAL_INTERFACE, dcnm, "node_ip")
            for node_info in json.loads(fabric_nodes_rsp):
                serial_number = node_info.get("serialNo")
                inband_ip_list = node_info.get("ipAddress", "")
                if (node_info["fabricName"].lower() != sa_fabric_name) or (not serial_number) or \
                        (number_to_ip.get(serial_number)) or (not inband_ip_list):
                    continue

                # multiple ipv4 and ipv6 inb ips may be present in this key,
                # ex: {..., "ipAddress": "1.1.1.1/8 2.2.2.2/8 000ca:0014::000d:0009:000d", ...}
                inband_ip_list = inband_ip_list.split()
                if len(inband_ip_list) > 0:
                    inband_ip = inband_ip_list[0].split("/")[0]
                    number_to_ip[str(serial_number)] = str(inband_ip)
        except Exception as e:
            self.logger.warning("Unable to create inband ip mapping due to: %s"%str(e))
        return number_to_ip

    def discoverStandaloneFabricNodes(self):
        switches = []
        node_ids = set()
        for dcnm in self.sa_topo_args.dcnms:
            try:
                sa_fabric_name = self.sa_topo_args.sa_fabric.lower()
                fabric_nodes_rsp = self.results_stash.lookupNodeQueries(QueryId.NX_FABRIC_DCNM_INVENTORY, dcnm,
                                                                        "node_ip")
                serial_number_to_inb = self.createInbandToNodeDict(dcnm, sa_fabric_name)

                for node_info in json.loads(fabric_nodes_rsp):
                    if node_info["fabricName"].lower() != sa_fabric_name:
                        continue
                    ip = node_info['ipAddress']
                    node_name = node_info['logicalName']
                    node_role = node_info['switchRole']
                    node_oob_ip = self.getResolvedHost(ip)
                    node_oob_ip = self.nat_public_to_private_translation(node_oob_ip)
                    serial_number = node_info['serialNumber']
                    node_id = GlobalUtils.generateNodeId(node_name=serial_number,
                                                     node_ids=node_ids)
                    node_inband_ip = serial_number_to_inb.get(serial_number, "0.0.0.0")

                    existing_node_ip = self.topology.getExistingNodeIp(
                                        node_name, node_oob_ip, node_inband_ip, node_name)
                    if existing_node_ip:
                        self.logger.info("TopoNode already created node_dn :%s" % node_dn)
                    node_ip = "0.0.0.0"

                    # Update the node_ip to the preferred node_ip interface
                    # or to the ip that already exists
                    if existing_node_ip:
                        node_ip = existing_node_ip
                    elif self.getConnectionPreferencePrimary() == ConnectionPreference.INBAND:
                        node_ip  = node_inband_ip
                    if node_ip == "0.0.0.0" or self.getConnectionPreferencePrimary() == ConnectionPreference.OOB:
                        node_ip  = node_oob_ip

                    update_version = False
                    if node_role in [LEAF, 'border', 'core router', 'aggregation', 'access']:
                        node_type = STANDALONE_LEAF
                        self.sa_topo_args._parseStandaloneNodes(
                            STANDALONE_LEAF, self.sa_topo_args.user, node_ip)
                        switches.append(node_ip)
                        update_version = True
                    elif node_role in [SPINE, 'border spine']:
                        node_type = STANDALONE_SPINE
                        self.sa_topo_args._parseStandaloneNodes(
                            STANDALONE_SPINE, self.sa_topo_args.user, node_ip)
                        switches.append(node_ip)
                        update_version = True

                    if update_version is True and node_ip not in ["0.0.0.0", "::"]:
                        version_idx = node_info['displayHdrs'].index('Release')
                        # standalone leaf/switch version in the format 9.3(2) etc
                        version_str = node_info['displayValues'][version_idx]
                        self.topology.createTopoNode(node_ip, node_name)
                        if version_str:
                            version = version_str.split("(")
                            self.topology.updateTopoNode(node_ip, "version", version[0])
                        self.topology.updateStandaloneTopoNode(
                            node_ip, self.nat_box, node_id, node_type,
                            node_name, self.sa_topo_args.sa_fabric)
                        self.topology.updateTopoNode(node_ip, "oob_ip", node_oob_ip)
                        self.topology.updateTopoNode(node_ip, "inband_ip", node_inband_ip)

            except Exception as e:
                self.logger.warning("One or more dcnm queries failed, Reason: " + str(e))

            finally:
                self.topology.updateTopoNode(dcnm,"contains_leaves_and_spines", switches)

    def runForVariousDcnmVersions(self, collector):
        # create topo node list with copy nodes and change version
        temp_node_list = []
        temp_id_counter = 0
        for dcnm in self.topology.topo_node_list.values():
            for version in DcnmVersionApiUtils.getSampleVersionForApis():
                node_copy = self.topology.quickCopyNode(dcnm, "-V"+version, temp_id_counter)
                temp_id_counter += 1
                node_copy.setSaFabric(self.sa_topo_args.sa_fabric)
                node_copy.setVersion(version)
                node_copy.setLoopbackInterface(dcnm.getLoopbackInterface())
                temp_node_list.append(node_copy)

        collector.setTopoNodeList(temp_node_list)
        collector.setMaxThreads(len(temp_node_list))
        collector.process()

        return collector.getNodeCollectionStats()


    def setDcnmSampleVersion(self, stats):
        # expecting only one type of version to succeed
        num_dcnms = len(list(self.topology.topo_node_list.values()))
        num_login_success = len(list(filter(lambda x: x.getRestLogin(), stats)))
        if num_login_success > num_dcnms:
            raise Exception("Multiple logins for different DCNM versions succeeded, unable to determine which version to use")
        elif num_login_success == 0:
            self.logger.warning("Unable to login into any DCNMs")

        for s in stats:
            if s.getRestLogin():
                stats_node = s.getNode()
                dcnm = self.topology.topo_node_list.get(stats_node.node_ip)
                version = stats_node.getVersion()
                dcnm.setVersion(version)
                self.logger.info("Setting version: %s for dcnm: %s, nodeId: %s"%(version, dcnm.getNodeIp(), dcnm.getNodeId()))

    def deduceDcnmVersion(self):
        node_ids = set()
        for dcnm in self.sa_topo_args.dcnms:
            self.resolved_input_ips.append(dcnm)
            node_ip = self.getResolvedHost(dcnm)
            node_ip = self.nat_public_to_private_translation(node_ip)
            self.topology.createTopoNode(node_ip)
            node_id = GlobalUtils.generateNodeId(
                node_name=dcnm, node_ids=node_ids)
            self.topology.updateStandaloneTopoNode(
                node_ip, self.nat_box, node_id, DCNM,
                dcnm, self.sa_topo_args.sa_fabric)
            self.topology.updateTopoNode(node_ip, "loopback_interface", self.loopback_interface)

        if len(self.topology.topo_node_list) == 0:
            return

        collector = GenericCollector(
            logger=self.logger,
            user=self.user,
            password=self.password,
            partition_index=0,
            partition_count=1,
            login_time_out=self.login_time_out,
            query_time_out=self.query_time_out,
            node_time_out=self.node_time_out,
            apic_login_time_out=self.apic_login_time_out,
            apic_query_time_out=self.apic_query_time_out,
            apic_node_time_out=self.apic_node_time_out,
            max_threads=min(self.max_threads,
                            len(self.topology.topo_node_list)),
            cnae_mode=_STANDALONE,
            lan_username=self.lan_username,
            lan_password=self.lan_password,
            leaf_list=self.leaf_list)

        collector.setExcludeQueryIds([], exclude_all=True) # queries will not be made
        collector.setOptimizedQuery(False)

        stats = self.runForVariousDcnmVersions(collector)
        self.setDcnmSampleVersion(stats)
        self.logger.info("Finished deducing dcnm version")


    def collectStandaloneTopologyQueries(self):
        collector = GenericCollector(
            logger=self.logger,
            user=self.user,
            password=self.password,
            partition_index=0,
            partition_count=1,
            login_time_out=self.login_time_out,
            query_time_out=self.query_time_out,
            node_time_out=self.node_time_out,
            apic_login_time_out=self.apic_login_time_out,
            apic_query_time_out=self.apic_query_time_out,
            apic_node_time_out=self.apic_node_time_out,
            max_threads=min(self.max_threads,
                            len(self.topology.topo_node_list)),
            cnae_mode=_STANDALONE,
            lan_username=self.lan_username,
            lan_password=self.lan_password,
            leaf_list=self.leaf_list)

        query_ids = FilterQueryIds.getDcnmTopologyQueryIdList()
        collector.setFilterQueryIds(query_ids)
        collector.setTopoNodeList(list(self.topology.topo_node_list.values()))
        collector.setOptimizedQuery(False)
        collector.process()

        results = collector.getResults()
        self.results_stash.addQueryResults(results)
        stats = collector.getNodeCollectionStats()
        self.collection_stats_stash.addCollectionStats(stats)

    def collectMsoTopologyQueries(self):
       self.logger.info("Collecting queries for topology discovery")
       topo_node_list = []
       node_ids = set()
       for each_mso in self.input_apic_ips:
           self.logger.info("Collecting queries for topology discovery : %s" % each_mso)
           x = self.getResolvedHost(each_mso)
           x = self.nat_public_to_private_translation(x)
           node = Node(x)
           node.setNodeRole(MSO)
           node.setNodeId(GlobalUtils.generateNodeId(
               node_name=each_mso, node_ids=node_ids))
           node.setNodeName("mso") #TODO: need to change nodeName
           node.setNatIP(x, self.nat_box)  # set ip/port for nat
           topo_node_list.append(node)

       collector = GenericCollector(
           self.logger,
           self.user,
           self.password,
           0,
           1,
           self.login_time_out,
           self.query_time_out,
           self.node_time_out,
           self.apic_login_time_out,
           self.apic_query_time_out,
           self.apic_node_time_out,
           max_threads=min(self.max_threads,
                           len(self.input_apic_ips)),
           cnae_mode=self.cnae_mode)

       # MSO only queries
       query_ids = FilterQueryIds.getMsoTopologyQueryIdList()
       collector.setFilterQueryIds(query_ids)
       collector.setTopoNodeList(topo_node_list)
       collector.setOptimizedQuery(False)
       collector.process()
       results = collector.getResults()
       self.results_stash.addQueryResults(results)
       stats = collector.getNodeCollectionStats()
       self.collection_stats_stash.addCollectionStats(stats)

    def collectTopologyQueries(self):
        self.logger.info("Collecting queries for topology discovery")
        topo_node_list = []
        for each_apic in self.input_apic_ips:
            x = self.getResolvedHost(each_apic)
            x = self.nat_public_to_private_translation(x)
            node = Node(x)
            node.setNodeRole(CONTROLLER)
            # First time node_id and node_name are not known until login is
            # done
            node.setNodeId(0)
            node.setNodeName("unkown")
            node.setNatIP(x, self.nat_box)  # set ip/port for nat
            topo_node_list.append(node)

        collector = GenericCollector(
            self.logger,
            self.user,
            self.password,
            0,
            1,
            self.login_time_out,
            self.query_time_out,
            self.node_time_out,
            self.apic_login_time_out,
            self.apic_query_time_out,
            self.apic_node_time_out,
            max_threads=min(self.max_threads,
                            len(self.input_apic_ips)),
            cnae_mode = self.cnae_mode)
        # APIC only queries
        query_ids = FilterQueryIds.getTopologyQueryIdList()

        collector.setFilterQueryIds(query_ids)
        collector.setTopoNodeList(topo_node_list)
        collector.setOptimizedQuery(False)
        collector.process()
        results = collector.getResults()
        self.results_stash.addQueryResults(results)
        stats = collector.getNodeCollectionStats()
        self.collection_stats_stash.addCollectionStats(stats)

    def getQuorumNode(self):
        quorum_node = None
        for each_ip in self.topology.topo_node_list:
            node = self.topology.topo_node_list[each_ip]
            if node.node_quorum is True:
                quorum_node = node
                break
        return quorum_node

    # Disover other controllers/spines/leafs in sys
    # Data consistent on the quorum ip
    def discoverNodeIp(self, quorum_ip):
        mgmt_node_rsp = self.results_stash.lookupNodeQueries(
            QueryId.LOGICAL_MGMTRSOOBSTNODE_XML, quorum_ip, "node_ip")

        oob_mgmt_address = ParseUtils.findAll(
            self, mgmt_node_rsp, "mgmtRsOoBStNode")
        top_system_rsp = self.results_stash.lookupNodeQueries(
            QueryId.LOGICAL_TOPSYSTEM_XML, quorum_ip, "node_ip")
        top_system = ParseUtils.findAll(self, top_system_rsp, "topSystem")
        oob_node_dn_ip_map = {}
        top_system_dn_oob_ip_map = {}
        top_system_dn_inband_ip_map = {}
        for each in top_system:
            node_id = ParseUtils.getAttribute(self, each, "id")
            pod_id = ParseUtils.getAttribute(self, each, "podId")
            node_dn = "topology/" + "pod-" + \
                str(pod_id) + "/node-" + str(node_id)
            if node_dn not in top_system_dn_oob_ip_map:
                top_system_dn_oob_ip_map[node_dn] = ParseUtils.getAttribute(self, each, "oobMgmtAddr")
            if node_dn not in top_system_dn_inband_ip_map:
                top_system_dn_inband_ip_map[node_dn] = ParseUtils.getAttribute(self, each, "inbMgmtAddr")
        for each in oob_mgmt_address:
            oob_ip = ParseUtils.getAttribute(self, each, 'addr')
            node_t_dn = ParseUtils.getAttribute(self, each, "tDn")
            if node_t_dn not in oob_node_dn_ip_map:
                oob_node_dn_ip_map[node_t_dn] = oob_ip.split('/')[0]
        return (oob_node_dn_ip_map, top_system_dn_oob_ip_map, top_system_dn_inband_ip_map)

    def getOobMgmtAddr(
            self,
            node_dn,
            oob_node_dn_ip_map,
            top_system_dn_ip_map):
        oob_mgmt_addr = "0.0.0.0"
        if node_dn in oob_node_dn_ip_map:
            oob_mgmt_addr = oob_node_dn_ip_map[node_dn]
        # Needed if APIC IP is not oob policy
        elif node_dn in top_system_dn_ip_map:
            oob_mgmt_addr = top_system_dn_ip_map[node_dn]
        else:
            self.logger.warning(
                "Skipping Node : %s, "
                "topSystem and mgmtRsOoBStNode both not found" %
                (node_dn))
        if oob_mgmt_addr == "0.0.0.0":
            self.logger.warning(
                "Skipping Node : %s, OOB Management address NOT configured" %
                (node_dn))
        return oob_mgmt_addr

    def getInbandMgmtAddr(
            self,
            node_dn,
            top_system_inband_ip_map):
        if node_dn in top_system_inband_ip_map:
            return top_system_inband_ip_map[node_dn]
        else:
            return "0.0.0.0"

    def addFabricNode(self, fabric_node, configured_ip_map, top_system_oob_ip_map, top_system_inband_ip_map):
        node_dn = ParseUtils.getAttribute(self, fabric_node, "dn")
        node_oob_ip = self.getOobMgmtAddr(
            node_dn, configured_ip_map, top_system_oob_ip_map)
        node_inband_ip = self.getInbandMgmtAddr(
            node_dn, top_system_inband_ip_map)

        node_adSt = ParseUtils.getAttribute(self, fabric_node, "adSt")
        node_role = ParseUtils.getAttribute(self, fabric_node, "role")
        # Fabric node has stale configuration
        if node_adSt == "off" and node_role == CONTROLLER:
            self.logger.warning("Fabric Node is admin down node_dn:%s" % node_dn)
            return
        node_name = ParseUtils.getAttribute(self, fabric_node, "name")
        # if node does not exist yet, then it return None, else returns the current ip
        # we do not quit here, because node might need to be updated
        existing_node_ip = self.topology.getExistingNodeIp(
                            node_dn, node_oob_ip, node_inband_ip, node_name)
        if existing_node_ip:
            self.logger.info("TopoNode already created node_dn :%s" % node_dn)
        node_ip = "0.0.0.0"

        # Update the node_ip to the preffered node_ip interface
        # or to the ip that already exists
        if existing_node_ip:
            node_ip = existing_node_ip
        elif self.getConnectionPreferencePrimary() == ConnectionPreference.INBAND:
            node_ip  = node_inband_ip
        if node_ip == "0.0.0.0" or self.getConnectionPreferencePrimary() == ConnectionPreference.OOB:
            node_ip  = node_oob_ip

        # create/update node attributes
        if node_ip != '0.0.0.0':
            if existing_node_ip == None:
                self.topology.createTopoNode(node_ip, node_dn)
            node_attrs = ["dn", "fabricSt", "id", "model", "name", "role"]
            for each_attr in node_attrs:
                attr_value = ParseUtils.getAttribute(
                    self, fabric_node, each_attr)
                if each_attr == 'id':
                    attr_value = int(attr_value)
                self.topology.updateTopoNode(node_ip, each_attr, attr_value)
            self.updateTopoNatConfiguration(node_ip)
            self.topology.updateTopoNode(node_ip, "oob_ip", node_oob_ip)
            self.topology.updateTopoNode(node_ip, "inband_ip", node_inband_ip)
            if node_role == CONTROLLER:
                self.topology.updateTopoNode(node_ip, "time", self.getApicTimeStamp())
                if not existing_node_ip:
                    self.topology.updateTopoNode(node_ip, "dns_look_up_hostname",
                                                 self.getDnsLookupHostname(node_ip))
        else:
            if existing_node_ip == None:
                self.topology.createMissingOobNode(node_ip, node_dn)
            node_attrs = ["fabricSt", "id", "model", "name", "role"]
            for each_attr in node_attrs:
                attr_value = ParseUtils.getAttribute(
                    self, fabric_node, each_attr)
                if each_attr == 'id':
                    attr_value = int(attr_value)
                self.topology.updateMissingOobNode(
                    node_ip, node_dn, each_attr, attr_value)
            self.topology.updateMissingOobNode(node_ip, node_dn, "oob_ip", node_oob_ip)
            self.topology.updateMissingOobNode(node_ip, node_dn, "inband_ip", node_inband_ip)

    def discoverFabricNodes(self):
        quorum_node = self.getQuorumNode()
        if quorum_node:
            quorum_ip = quorum_node.node_ip
            (configured_oob_ip_map, top_system_dn_oob_ip_map,
                top_system_dn_inband_ip_map) = self.discoverNodeIp(quorum_ip)
            fabric_nodes_rsp = self.results_stash.lookupNodeQueries(
                QueryId.LOGICAL_FABRICNODE_XML, quorum_ip, "node_ip")

            fabric_nodes = ParseUtils.findAll(
                self, fabric_nodes_rsp, "fabricNode")
            for each in fabric_nodes:
                try:
                    get_attr = lambda x: ParseUtils.getAttribute(self, each, x)
                    if (get_attr("fabricSt"), get_attr("adSt")) == ("disabled", "off"):
                        get_opt_attr = lambda x: ParseUtils.getAttribute(self, each, x, True)
                        self.logger.info("skipping discovery for disabled node with node id: %s, node ip: %s, node dn: %s"%(
                            get_opt_attr("id"), get_opt_attr("address"), get_opt_attr("dn")))
                        continue;
                    self.addFabricNode(
                        each, configured_oob_ip_map,
                        top_system_dn_oob_ip_map,
                        top_system_dn_inband_ip_map)
                except Exception as e:
                    self.logger.warning(
                        "Adding of fabric node failed , Reason " + str(e))
                    continue

    '''
    Determine asic types
    '''

    def getHardwareModel(self, node):
        asic_type = AsicType.UNKNOWN
        eqpt_lc_rsp = self.results_stash.lookupNodeQueries(QueryId.CONCRETE_LC,
                                                           node.node_id,
                                                           "node_id")

        eqpt_lc = ParseUtils.findAll(self, eqpt_lc_rsp, "eqptLC")

        model_name = ParseUtils.getAttribute(self, eqpt_lc[0], 'model')
        asic_type = AsicType.getAsicTypeFrmModelCatalog(model_name)
        if asic_type == AsicType.UNKNOWN and node.node_role == LEAF:
            self.logger.warning(
                "Unknown ToR model detected for Node: %s Model: %s" %
                (node.node_dn, model_name))
        return (asic_type, model_name)

    def getNodeFeatures(self, node):
        #the format of the dta expected is
        #{"totalCount":"1","imdata":[{"fmEntity": {"attributes": {"childAction": "","dn": "sys/fm",
        # "modTs": "2020-04-06T21:41:36.518+00:00","status": ""},"children": [{"fmVnSegment": {"attributes": {"adminSt": "enabled","childAction":
        # "","fmCfgFailedBmp": "","fmCfgFailedTs": "0","fmCfgState": "0","maxInstance": "1","modTs": "2020-04-06T21:42:55.327+00:00",
        # "operSt": "enabled","rn": "vnsegment","status": ""}}},{u'fmNvo': {u'attributes': {u'status': u'',
        # u'fmCfgFailedBmp': u'', u'fmCfgFailedTs': u'0', u'adminSt': u'enabled', u'fmCfgState': u'0', u'modTs': u'2020-04-06T21:42:55.411+00:00',
        # u'maxInstance': u'1', u'rn': u'nvo', u'operSt': u'enabled', u'childAction': u''}}}]

        enabled_features = []
        feature_rsp = self.results_stash.lookupNodeQueries(
            QueryId.NX_FABRIC_GET_SUPPORTED_FEATURE, node.node_id, "node_id")
        self.logger.debug("features Response with ast %s" %(feature_rsp))

        try:
            json_doc = json.loads(feature_rsp)
            imdata = json_doc['imdata']
            self.logger.debug("imdata Response %s" %(imdata))

            fmEntity = imdata[0]['fmEntity']
            children = fmEntity['children']
            self.logger.debug("chilrenf %s" %(children))
            feature_list = []

            for ch in children:
                ch_keys = []
                for k in ch.keys():
                    ch_keys.append(safely_decode_str(k))
                self.logger.debug("childnow %s and keysnow %s" %(ch, ch_keys))
                feature_list.extend(ch_keys)
                fea = ch[ch_keys[0]]
                self.logger.debug("featuredataobt %s " %(fea))
                attribute = fea['attributes']
                self.logger.debug("attribnow %s " %(attribute))
                status = attribute['adminSt']
                self.logger.debug("statusnow %s " %(status))
                if(status == 'enabled') :
                    enabled_features.append(str(ch_keys[0]))
        except Exception as e:
            traceback.print_stack()
            print('--------------')
            traceback.print_exc()
            self.logger.warning(
                ("Unable to get Features set for node %s" %
                 str(e)))

        self.logger.debug("Features enabled for %s switch : %s" %(node.node_dn, str(enabled_features)))
        return enabled_features


    '''
    Determine numbers of ethernet interfaces
    '''

    def getEthernetInterfaces(self, node):
        l1physif_rsp = self.results_stash.lookupNodeQueries(
            QueryId.CONCRETE_L1PHYSIF, node.node_id, "node_id")
        l1physif_list = ParseUtils.findAll(self, l1physif_rsp, "l1PhysIf")
        intf_list = []
        for l1physif in l1physif_list:
            eth_id = ParseUtils.getAttribute(self, l1physif, 'id')
            intf_list.append(eth_id)
        return intf_list

    def getFabricCardNumbersFromSpine(
            self, spine_node_dn, eqpt_fc_slot, eqpt_fc):
        fcs = []
        for each_fc_slot in eqpt_fc_slot:
            each_fc_slot_dn = each_fc_slot.attrib['dn']
            # ASK Chandra: Why are we appending a '/' here??
            phys_ids = [
                each_fc_slot.attrib['physId'] for x in eqpt_fc if each_fc_slot_dn +
                '/' in x.attrib['dn'] and x.attrib['operSt'] == 'online']
            fcs.extend(phys_ids)
        return fcs

    def getSpineFabricCard(self, node):
        eqpt_fc_rsp = self.results_stash.lookupNodeQueries(QueryId.CONCRETE_FC,
                                                           node.node_id,
                                                           "node_id")
        eqpt_fc = ParseUtils.findAll(self, eqpt_fc_rsp, "eqptFC")

        eqpt_fc_slot_rsp = self.results_stash.lookupNodeQueries(
            QueryId.CONCRETE_FCSlot, node.node_id, "node_id")

        eqpt_fc_slot = ParseUtils.findAll(self, eqpt_fc_slot_rsp, "eqptFCSlot")
        spine_fcs = self.getFabricCardNumbersFromSpine(
            node.node_dn, eqpt_fc_slot, eqpt_fc)

        return spine_fcs

    '''
    Determine Spine FCS/model
    '''

    def processSpineNodes(self):
        spine_nodes = [
            x for x in list(self.topology.topo_node_list.values())
            if x.node_role == SPINE or x.node_role == STANDALONE_SPINE]

        for spine in spine_nodes:
            spine_fcs = []
            asic_type = AsicType.UNKNOWN
            model_name = "UNKNOWN_MODEL"
            try:
                asic_type, model_name = self.getHardwareModel(spine)
            except Exception as e:
                self.logger.warning(
                    "Unable to determine spine model number, Reason: %s" %
                    str(e))
            finally:
                self.topology.updateTopoNode(
                    spine.node_ip, "asic_model", model_name)

            try:
                spine_fcs = self.getSpineFabricCard(spine)
            except Exception as e:
                self.logger.warning(
                    "Unable to determine spine model number, Reason: %s" %
                    str(e))
            finally:
                self.topology.updateTopoNode(spine.node_ip, "fcs", spine_fcs)
                node_stats = self.collection_stats_stash.getCollectionStats(
                    spine.getNodeIp())
                if node_stats:
                    reachable = node_stats[0].getReachable()
                    self.topology.updateTopoNode(
                        spine.node_ip, "is_reachable", reachable)

            if spine.node_role == 'standalone_spine' :
                try:
                    node_en_features = []
                    self.logger.info("Standalone spine, getting node features %s" %(spine.node_ip))
                    node_en_features = self.getNodeFeatures(spine)
                except Exception as e:
                    self.logger.warning(
                        "Unable to determine enabled spine features, Reason: %s" %
                        str(e))
                finally:
                    spine.enabled_features = node_en_features
                    self.logger.info("Node enabled features set for node %s are %s" %(spine.node_ip, str(spine.enabled_features)))


    '''
    Handle per leaf/spine failures
    '''

    def processLeafNodes(self):
        leaf_nodes = [
            x for x in list(self.topology.topo_node_list.values())
            if x.node_role == LEAF or x.node_role == STANDALONE_LEAF]
        for leaf in leaf_nodes:
            asic_type = AsicType.UNKNOWN
            model_name = "UNKNOWN_MODEL"

            try:
                asic_type, model_name = self.getHardwareModel(leaf)
            except Exception as e:
                self.logger.warning(
                    "Unable to determine leaf asic type, Reason: %s" %
                    str(e))
            finally:
                self.topology.updateTopoNode(
                    leaf.node_ip, "asic_type", asic_type)
                self.topology.updateTopoNode(
                    leaf.node_ip, "asic_model", model_name)
                self.topology.updateTopoNode(
                    leaf.node_ip, "asic_name", AsicType.getAsicTypeName(asic_type))
                node_stats = self.collection_stats_stash.getCollectionStats(
                    leaf.getNodeIp())
                if node_stats:
                    reachable = node_stats[0].getReachable()
                    self.topology.updateTopoNode(
                        leaf.node_ip, "is_reachable", reachable)

            try:
                intf_list = self.getEthernetInterfaces(leaf)
                self.topology.updateTopoNode(
                    leaf.node_ip, "intf_list", intf_list)
            except Exception as e:
                self.logger.warning(
                    "Unable to get leaf ethernet interfaces, Reason: %s" %
                    str(e))

            if leaf.node_role == 'standalone_leaf' :
                try:
                    node_en_features = []
                    self.logger.info("Standalone leaf, getting node features %s" %(leaf.node_ip))
                    node_en_features = self.getNodeFeatures(leaf)
                except Exception as e:
                    self.logger.warning(
                        "Unable to determine enabled leaf features, Reason: %s" %
                        str(e))
                finally:
                    leaf.enabled_features = node_en_features
                    self.logger.info("Node enabled features set for node %s are %s" %(leaf.node_ip, str(leaf.enabled_features)))


    def collectHardwareModel(self):
        topo_node_list = [
            x for x in list(self.topology.topo_node_list.values()) if x.node_role in [
                LEAF, SPINE]]
        collector = GenericCollector(
            self.logger,
            self.user,
            self.password,
            0,
            1,
            self.login_time_out,
            self.query_time_out,
            self.node_time_out,
            self.apic_login_time_out,
            self.apic_query_time_out,
            self.apic_node_time_out,
            max_threads=min(self.max_threads,
                            len(topo_node_list)),
            cnae_mode=self.cnae_mode)
        query_ids = FilterQueryIds.getHardwareModelQueryIds()
        collector.setFilterQueryIds(query_ids)
        collector.setTopoNodeList(topo_node_list)
        collector.setOptimizedQuery(False)
        collector.process()
        results = collector.getResults()
        self.results_stash.addQueryResults(results)
        stats = collector.getNodeCollectionStats()
        self.collection_stats_stash.addCollectionStats(stats)

    def collectSupportedFeatures(self):
        standalone_topo_node_list = [
            x for x in list(self.topology.topo_node_list.values()) if x.node_role in [
                'standalone_spine', 'standalone_leaf']]
        collector = GenericCollector(
            self.logger,
            self.user,
            self.password,
            0,
            1,
            self.login_time_out,
            self.query_time_out,
            self.node_time_out,
            self.apic_login_time_out,
            self.apic_query_time_out,
            self.apic_node_time_out,
            max_threads=min(self.max_threads,
                            len(standalone_topo_node_list)),
            cnae_mode=self.cnae_mode,
            lan_username=self.lan_username,
            lan_password=self.lan_password,
            leaf_list=self.leaf_list)
        query_ids = FilterQueryIds.getSupportedFeaturesQueryIdList()
        collector.setFilterQueryIds(query_ids)
        collector.setTopoNodeList(standalone_topo_node_list)
        collector.setOptimizedQuery(False)
        collector.process()
        results = collector.getResults()
        self.results_stash.addQueryResults(results)
        stats = collector.getNodeCollectionStats()
        self.collection_stats_stash.addCollectionStats(stats)

    def printTopologyInfo(self):
        leaf_roles = [LEAF, STANDALONE_LEAF]
        spine_roles = [SPINE, STANDALONE_SPINE]
        controller_roles = [CONTROLLER, DCNM, MSO]
        controller_role = ""
        if self.cnae_mode == _APIC:
            controller_role = "apic"
        elif self.cnae_mode == _MSO:
            controller_role = MSO
        else:
            controller_role = DCNM
        controllers = [x for x in list(self.topology.topo_node_list.values())
                       if x.node_role in controller_roles]
        leafs = [x for x in list(self.topology.topo_node_list.values())
                 if x.node_role in leaf_roles]
        spines = [x for x in list(self.topology.topo_node_list.values())
                  if x.node_role in spine_roles]
        self.logger.info(("Total %s discovered %d" % (controller_role,
                                                      len(controllers))))
        self.logger.info("++++++++++++++++++++++++++")
        self.logger.info("Topology information")

        self.logger.info("%s Information" % controller_role)
        for each_controller in controllers:
            self.logger.info(str(each_controller))
        self.logger.info("------------------")
        self.logger.info("Switch Information")
        for each_leaf in leafs:
            self.logger.info(str(each_leaf))
        self.logger.info("------------------")
        self.logger.info("Spine Information")
        for each_spine in spines:
            self.logger.info(str(each_spine))
        self.logger.info("------------------")
        self.logger.info("+++++++++++++++++++++++++++")


    '''
    node - only quorum apic nodes have fabric name set.
    '''

    def setControllerFabricName(self, apic_ip):
        try:
            logical_clusters_rsp = self.results_stash.lookupNodeQueries(
                QueryId.LOGICAL_INFRACONT, apic_ip, "node_ip")
        except BaseException:
            self.logger.warning(
                "Failed query infraCont. Ignoring setting fabric name for apic: " +
                str(apic_ip))
            return
        clusters = ParseUtils.findAll(self, logical_clusters_rsp, "infraCont")

        for cluster in clusters:
            cluster_dn = ParseUtils.getAttribute(self, cluster, "dn")
            fabric_name = ParseUtils.getAttribute(self, cluster, "fbDmNm")
            self.logger.debug("Fabric Name: " + str(fabric_name))

            for node_list in [self.topology.topo_node_list, self.topology.login_failed_node_list]:
                for each_node in list(node_list.keys()):
                    node = node_list[each_node]
                    if node.node_dn + '/' in cluster_dn:
                        self.topology.updateTopoNode(
                            node.node_ip, "fabric_name", fabric_name)

    '''
    node - only quorum apic nodes have fabric uuid set.
    '''

    def setControllerUUID(self, apic_ip):
        cluster_elements_rsp = self.results_stash.lookupNodeQueries(
            QueryId.LOGICAL_INFRAWINODE, apic_ip, "node_ip")
        cluster_elements = ParseUtils.findAll(self, cluster_elements_rsp,
                                              "infraWiNode")
        for each_cluster_element in cluster_elements:
            cluster_element_dn = ParseUtils.getAttribute(
                self, each_cluster_element, "dn")

            # skipping elements topology/pod-1/node-1/av/node-2 (with different
            # node values)
            split_strs = cluster_element_dn.split('/')
            node1, node2 = split_strs[2], split_strs[4]
            if not node2 == node1:
                continue

            chassis = ParseUtils.getAttribute(
                self, each_cluster_element, "chassis")
            self.logger.debug("Fabric uuid (chassis): " + str(chassis))
            for each_node in list(self.topology.topo_node_list.keys()):
                node = self.topology.topo_node_list[each_node]
                if node.node_dn + '/' in cluster_element_dn:
                    self.topology.updateTopoNode(
                        node.node_ip, "fabric_uuid", chassis)

    '''
    node - can be either a quorum node or non-quorum  for apic versions
    '''

    def setControllerVersion(self, apic_ip=None):
        if apic_ip:
            controller_version_rsp = self.results_stash.lookupNodeQueries(
                QueryId.LOGICAL_APICVERSION, apic_ip, "node_ip")
            controller_info = ParseUtils.getChildren(
                self, controller_version_rsp, "firmwareCtrlrRunning")
            for each_controller in controller_info:
                # dn : topology/pod-1/node-1/sys/ctrlrfwstatuscont/ctrlrrunning
                node_dn = '/'.join(ParseUtils.getAttribute(self,
                                                           each_controller["firmwareCtrlrRunning"],
                                                           "dn").split("/")[0:3])
                # apic version = 2.0(2h)
                node_version = ParseUtils.getAttribute(
                    self, each_controller["firmwareCtrlrRunning"], "version").split('(')[0]
                self.topology.updateNodeVersion(node_dn, node_version)

    def setDcnmControllerVersion(self):
        for dcnm in self.sa_topo_args.dcnms:
            if DcnmVersionApiUtils.getPrefixApi(self.topology.topo_node_list.get(
                    dcnm).getVersion()):
                continue;

            dcnm_version_rsp = self.results_stash.lookupNodeQueries(
                QueryId.NX_FABRIC_DCNM_VERSION, dcnm, "node_ip")
            dcnm_info = json.loads(dcnm_version_rsp)
            if dcnm_info:
                version_str = dcnm_info['Dcnm-Version']
                #dcnm version is in the format '11.2(2)' etc
                version = version_str.split("(")
                self.topology.updateTopoNode(dcnm, "version", version[0])

    '''
    ip here should be only quorum ip of apic
    '''

    def setLeafSpineVersion(self, quorum_ip=None):
        switch_version_rsp = self.results_stash.lookupNodeQueries(
            QueryId.LOGICAL_SWITCHVERSION, quorum_ip, "node_ip")
        switch_info = ParseUtils.getChildren(
            self, switch_version_rsp, "firmwareRunning")
        for each_switch in switch_info:
            # switch dn : topology/pod-1/node-1017/sys/fwstatuscont/running
            node_dn = '/'.join(ParseUtils.getAttribute(self,
                                                       each_switch["firmwareRunning"],
                                                       "dn").split('/')[0:3])
            # swith versin = n9000-12.0(2h)
            node_version = ParseUtils.getAttribute(
                self, each_switch["firmwareRunning"], "version").split('-')[-1].split('(')[0]
            self.topology.updateNodeVersion(node_dn, node_version)

            # Set all inactive node versions, by getting the info from switch
            # itself
        for each_ip in list(self.topology.topo_node_list.keys()):
            node = self.topology.topo_node_list[each_ip]
            if node.node_role == CONTROLLER:
                continue

            try:
                if node.node_fabric_st != "active":
                    switch_inactive_rsp = self.results_stash.lookupNodeQueries(
                        QueryId.CONCRETE_SWITCHVERSION, node.node_ip, "node_ip")
                    switch_inactive = ParseUtils.getChildren(
                        self, switch_inactive_rsp, "firmwareRunning")
                    node_version = ParseUtils.getAttribute(
                        self, switch_inactive[0]["firmwareRunning"], "version").split('-')[-1].split('(')[0]
                    self.topology.updateNodeVersion(node.node_dn, node_version)
            except BaseException:
                self.logger.warning(
                    "Setting version to default, missing switch verion query")
                self.topology.updateNodeVersion(node.node_dn, "UNKNOWN")

    def setIsConfigured(self):
        for each_ip in self.topology.topo_node_list:
            if self.nat_private_to_public_translation(
                    each_ip) in self.resolved_input_ips:
                self.topology.updateTopoNode(each_ip, "is_configured", True)
            else:
                self.topology.updateTopoNode(each_ip, "is_configured", False)

    def setIsSupported(self):
        for node_list in [self.topology.topo_node_list, self.topology.login_failed_node_list]:
            for each_ip in node_list:
                node = node_list[each_ip]
                if node.node_role in [CONTROLLER, DCNM]:
                    if node.node_version in self.version:
                        self.topology.updateTopoNode(each_ip, "is_supported", True)
                    else:
                        self.logger.info(
                            "Candid doesn't support the %s version:%s node_id: %s,supported version: %s" %
                            (self.cnae_mode, node.node_version, node.node_id, self.version))

                        self.topology.updateTopoNode(
                            each_ip, "is_supported", False)
                elif node.node_role in [LEAF, SPINE, STANDALONE_LEAF, STANDALONE_SPINE]:
                    #"UNKNOWN" is because , we have some old customer data sets that do not contain switch version query
                    if node.node_version in self.switch_version or \
                       node.node_version == "UNKNOWN":
                        self.topology.updateTopoNode(each_ip, "is_supported", True)
                    else:
                        self.topology.updateTopoNode(
                            each_ip, "is_supported", False)
                        self.logger.info(
                            "Candid doesn't support the switch version: %s node_id: %s,supported versions: %s" %
                            (node.node_version, node.node_id, self.switch_version))

    '''
    Query result of APIC version used to set the login.
    '''

    def setIsLoginControllers(self):
        # Find all the apic nodes for which we did not login and was
        # discovered
        controllers = [x for x in list(self.topology.topo_node_list.values()) if x.node_role in [
            CONTROLLER]]
        topo_node_list = []
        for each_node in controllers:
            if each_node.node_role == CONTROLLER and each_node.node_is_configured is False:
                topo_node_list.append(each_node)

        collector = GenericCollector(
            self.logger,
            self.user,
            self.password,
            0,
            1,
            self.login_time_out,
            self.query_time_out,
            self.node_time_out,
            self.apic_login_time_out,
            self.apic_query_time_out,
            self.apic_node_time_out,
            max_threads=min(
                self.max_threads,
                len(topo_node_list)),
            cnae_mode=self.cnae_mode)
        query_ids = [QueryId.LOGICAL_APICVERSION]
        collector.setFilterQueryIds(query_ids)
        collector.setTopoNodeList(topo_node_list)
        collector.setOptimizedQuery(False)
        collector.process()
        results = collector.getResults()
        self.results_stash.addQueryResults(results)
        stats = collector.getNodeCollectionStats()
        self.collection_stats_stash.addCollectionStats(stats)

        '''
        Set login for all controllers
        '''
        for each_ip in self.topology.topo_node_list:
            node = self.topology.topo_node_list[each_ip]
            if node.node_role == CONTROLLER:
                self.topology.updateTopoNode(
                    each_ip, "is_login", self.checkLogin(each_ip))
                node_collection_stats = self.collection_stats_stash.getCollectionStats(
                    node.getNodeIp())
                if node_collection_stats:
                    reachable = node_collection_stats[0].getReachable()
                    self.topology.updateTopoNode(each_ip, "is_reachable",
                                                 reachable)
                else:
                    self.topology.updateTopoNode(
                        each_ip, "is_reachable", False)

    def setIsLogin(self, cnae_mode):
        if cnae_mode == _APIC:
            self.setIsLoginControllers()
        self.setIsLoginSwitches()

    def setIsLoginNxFabric(self, each_ip, node):
        if node.node_connection_info:
            if node.node_role in [DCNM]:
                login = node.node_connection_info[0].connection_rest_login
            elif node.node_role in [STANDALONE_LEAF,STANDALONE_SPINE]:
                login = (node.node_connection_info[0].connection_rest_login
                         and node.node_connection_info[0].connection_ssh_login)
            self.topology.updateTopoNode(each_ip, "is_login", login)
            reachable = node.node_connection_info[0].connection_reachable
            self.topology.updateTopoNode(each_ip, "is_reachable",
                                     reachable)

    def setIsLoginMsoFabric(self, each_ip, node):
        if node.node_connection_info:
            login = node.node_connection_info[0].connection_rest_login
            self.topology.updateTopoNode(each_ip, "is_login", login)
            reachable = node.node_connection_info[0].connection_reachable
            self.topology.updateTopoNode(each_ip, "is_reachable",
                                         reachable)

    def setIsLoginSwitches(self):
        '''
        Switch / Spine setting
        '''
        for each_ip in self.topology.topo_node_list:
            node = self.topology.topo_node_list[each_ip]
            if node.node_role in [DCNM, STANDALONE_LEAF,STANDALONE_SPINE]:
                self.setIsLoginNxFabric(each_ip, node)
            elif node.node_role in [LEAF, SPINE]:
                self.topology.updateTopoNode(
                    each_ip, "is_login", self.checkLogin(each_ip))
            elif node.node_role in [MSO]:
                self.setIsLoginMsoFabric(each_ip, node)

    '''
    If only one APIC is given which is part of majority, we need to set other discovered
    APICs state as in_quorum
    '''

    def setQuorum(self, quorum_node):
        healthy_cluster_elements = self.getHealthyClusterElements(
            quorum_node.node_ip, quorum_node.node_pod_id, quorum_node.node_id)
        healthy_node_ids = [int(ParseUtils.getAttribute(self, x, "dn").split(
            '/')[-1].split('-')[1]) for x in healthy_cluster_elements]
        self.logger.info("Healthy node ids :%s" % healthy_node_ids)
        admin_size = quorum_node.node_admin_cluster_size
        current_size = quorum_node.node_current_cluster_size
        concrete_size = quorum_node.node_concrete_cluster_size
        for each_ip in self.topology.topo_node_list:
            node = self.topology.topo_node_list[each_ip]
            if node.node_role == CONTROLLER:
                if node.node_quorum is None:
                    if node.node_id in healthy_node_ids:
                        # For apics that are discovered, set the admin/current
                        # size from quorum node
                        if node.node_admin_cluster_size == 0:
                            self.topology.updateTopoNode(
                                each_ip, "admin_cluster_size", admin_size)
                        if node.node_current_cluster_size == 0:
                            self.topology.updateTopoNode(
                                each_ip, "current_cluster_size", current_size)
                        if node.node_concrete_cluster_size == 0:
                            self.topology.updateTopoNode(
                                each_ip, "concrete_cluster_size", concrete_size)
                        self.topology.updateTopoNode(each_ip, "quorum", True)
                    else:
                        self.topology.updateTopoNode(each_ip, "quorum", False)
                        self.topology.updateTopoNode(
                            each_ip, "current_cluster_size", 0)
                        self.topology.updateTopoNode(
                            each_ip, "concrete_cluster_size", 0)
                        self.topology.updateTopoNode(
                            each_ip, "admin_cluster_size", admin_size)

    def updateNodeConnectionPreferences(self):
            c_p_h = ConnectionPreference.ConnectionPreferenceHandler(
                self.logger, self.topology.topo_node_list,
                self.topology.missing_node_ip_list, self.nat_box, self.cnae_mode)
            info = (self.user, self.password, 0, 1,
                    self.login_time_out, self.query_time_out, self.node_time_out,
                    self.apic_login_time_out, self.apic_query_time_out,
                    self.apic_node_time_out, self.max_threads, self.lan_username, self.lan_password, self.leaf_list)
            c_p_h.processConnectionPreference(info, self.getConnectionPreferenceSecondary())
            self.topology.topo_node_list = c_p_h.getLoginSuccessNodes()
            self.topology.topo_node_list.update(c_p_h.getLoginFailedNodes())
            # self.topology.login_failed_node_list = c_p_h.getLoginFailedNodes()
            self.topology.missing_node_ip_list = c_p_h.getMissingConnectionIps()

    def process(self):
        # Step 1: Given input APIC ip addresses, make topology queries in parallel using just the node_ip of apics
        #        Node_id set to 0 , since we do not know yet
        if self.cnae_mode == _APIC:
            if self.input_apic_ips:
                try:
                    self.collectTopologyQueries()
                    self.detectQuorum()
                    if self.isConcreteSizeConsistent():
                        self.setQuorumForConfiguredApics()
                        self.discoverFabricNodes()
                        self.updateNodeConnectionPreferences()
                        self.collectHardwareModel()
                        self.processLeafNodes()
                        self.processSpineNodes()
                        quorum_node = self.getQuorumNode()
                        if quorum_node is not None:
                            node_ip = quorum_node.node_ip
                            self.setQuorum(quorum_node)
                            self.setControllerVersion(node_ip)
                            self.setLeafSpineVersion(node_ip)
                            self.setControllerFabricName(node_ip)
                            self.setControllerUUID(node_ip)
                        self.setIsConfigured()
                        self.setIsLogin(cnae_mode=_APIC)
                        self.setIsSupported()
                    self.printTopologyInfo()

                except Exception as e:
                    traceback.print_stack()
                    print('--------------')
                    traceback.print_exc()
                    raise TopologyExplorerException(
                        "Topology discovery failed, Reason: %s" % str(e))

            else:
                raise TopologyExplorerException(
                    "Address resolution of APIC's failed", self.input_apic_ips)

        elif self.cnae_mode == _STANDALONE:
            try:
                self.deduceDcnmVersion()
                self.collectStandaloneTopologyQueries()
                self.discoverStandaloneFabricNodes()
                self.setDcnmControllerVersion()
                self.updateNodeConnectionPreferences()
                self.collectSupportedFeatures()
                self.processLeafNodes()
                self.processSpineNodes()
                self.setIsConfigured()
                self.setIsLogin(cnae_mode=_STANDALONE)
                self.setIsSupported()
                self.printTopologyInfo()

            except Exception as e:
                traceback.print_stack()
                print('--------------')
                traceback.print_exc()
                raise TopologyExplorerException(
                    "Topology discovery failed, Reason: %s" % str(e))

        elif self.cnae_mode == _MSO:
            if self.input_apic_ips:
                try:
                    self.collectMsoTopologyQueries()
                    # TODO: self.discoverMsoFabricNodes() needed??
                    self.detectMsoQuorum()
                    self.updateNodeConnectionPreferences()
                    self.setIsConfigured()
                    self.setIsLogin(cnae_mode=_MSO)
                    # self.setMsoControllerVersion() TODO:implement function
                    self.setIsSupported()
                    self.printTopologyInfo()
                except Exception as e:
                    traceback.print_stack()
                    print('--------------')
                    traceback.print_exc()
                    raise TopologyExplorerException(
                        "Topology discovery failed, Reason: %s" % str(e))
            else:
                raise TopologyExplorerException(
                    "Address resolution of MSO's failed", self.input_apic_ips)

class ConnectionPreference:
    UNKNOWN = 0
    OOB = 1
    INBAND = 2

    @staticmethod
    def getConnectionPreferenceType(connection_preference):
        if connection_preference:
            if connection_preference.lower() == "outofband":
               return ConnectionPreference.OOB
            elif connection_preference.lower() == "inband":
               return ConnectionPreference.INBAND
        return ConnectionPreference.UNKNOWN

    class ConnectionPreferenceHandler:
        def __init__(self, logger, topo_node_dict, missing_oob_dict,
                     nat=None, cnae_mode=_APIC):
            self.nat = nat
            self.logger = logger
            self.passing_nodes = {}
            self.failing_nodes = {}
            # easy way to deep copy dictionaries is to update an empty dict
            # but must be instantiated first
            self.retry_login_ips = {}
            self.retry_login_ips.update(topo_node_dict)
            self.missing_current_connection_ip = {}
            self.cnae_mode = cnae_mode
            if missing_oob_dict.get("0.0.0.0"):
                self.missing_current_connection_ip.update(missing_oob_dict.get("0.0.0.0"))

        def processConnectionPreference(self, info, secondary_preference):
            # flow:
            # 1) try to login to all nodes in retry_login_ips
            # 2) move all nodes from missing_conn to retry_login
            # 3) add connection info to nodes that have been processed
            # 3) move ips from retry_login to passing nodes or missing_conn
            # 4) if node stays in retry_login, switch ip to next connection pref ip
            # 5) repeat steps 1 to 4 until all nodes have been filtered to passing/failing nodes
            (user, password, partition_index, partition_count,
                login_time_out, query_time_out, node_time_out,
                apic_login_time_out, apic_query_time_out,
                apic_node_time_out, max_threads, lan_username, lan_password, leaf_list) = info

            # if login fails, switch to next preference
            for next_connection_preference in [secondary_preference, None]:
                if len(self.retry_login_ips) > 0:
                    collector = GenericCollector(
                        self.logger,
                        user,
                        password,
                        partition_index,
                        partition_count,
                        login_time_out,
                        query_time_out,
                        node_time_out,
                        apic_login_time_out,
                        apic_query_time_out,
                        apic_node_time_out,
                        max_threads=min(max_threads,len(self.retry_login_ips)),
                        cnae_mode=self.cnae_mode,
                        lan_username=lan_username,
                        lan_password=lan_password,
                        leaf_list=leaf_list)
                    collector.setExcludeQueryIds([], exclude_all=True) # queries will not be made
                    collector.setTopoNodeList(list(self.retry_login_ips.values()))
                    collector.setOptimizedQuery(False)
                    collector.process()
                    # do not need query results
                    stats = collector.getNodeCollectionStats() # do we want to save this stuff?
                    # add node_connection_information and move successful login nodes to passing_nodes
                    # move missing_oob nodes to retry_login_ips to switch their ips into secondaryIps
                    self.retry_login_ips.update(self.missing_current_connection_ip)
                    self.missing_current_connection_ip = {}
                    # switch to next_connection_preference if the preference is available
                    self.switchAndFilterIps(next_connection_preference, stats)
            self.organizeNodes()

        # updates node_connection_informatio for node in retry_login_ips
        def addConnectionInformation(self, stats):
            ip = stats.getNode().node_ip
            node = self.retry_login_ips.get(ip)
            if node == None:
                return;
            preference_used = node.getConnectionPreferenceUsed()
            connection_information = ConnectionInformation(preference_used, node.node_ip, node.node_port)
            connection_information.setReachable(stats.getReachable())
            connection_information.setRestLogin(stats.getRestLogin())
            connection_information.setSshLogin(stats.getSshLogin())
            connection_information.setNatAttributes(node.node_public_ip, node.node_public_port)
            node.addNodeConnectionInfo(connection_information)

        # add connection information for the node's current connection
        # and then move login success nodes to passing node lists
        def parseCollectionStats(self, stats, preference):
            for node_stat in stats:
                # add collection information to nodes that have been processed
                self.addConnectionInformation(node_stat)

                # filter nodes between passing, missing ip, or retry_login_ips
                ip = node_stat.getNode().node_ip
                if self.retry_login_ips.get(ip):
                    node = self.retry_login_ips.pop(ip)
                    if node_stat.getSshLogin() and node_stat.getRestLogin():
                        self.passing_nodes[ip] = node
                    else:
                        # if next preference ip is current ip, move to missing ip list
                        # else, keep in retry ips to switch ip
                        new_ip = node.getPreferredNodeIp(preference)
                        if new_ip == "0.0.0.0" or node.node_ip != new_ip:
                            self.retry_login_ips[ip] = node
                        else:
                            self.missing_current_connection_ip[ip] = node
                else:
                    self.logger.debug("{0} was not meant to be processed in generic collector".format(ip))

        def switchAndFilterIps(self, preference, stats):
            # both methods filter nodes from retry_login_ips to passing/retry/missing_ip node lists
            # add connection info and move login passed to passing or missing_current_connection
            self.parseCollectionStats(stats, preference)

            # switch ips in retry ips
            self.switchIps(preference)

        def switchIps(self, preference):
            # if preference is None, then there is no other ip to switch to
            # and add to failing_nodes
            if preference:
                for ip in list(self.retry_login_ips.keys()):
                    node = self.retry_login_ips.pop(ip)
                    # switch ip to next connection preference, if available
                    new_ip = node.getPreferredNodeIp(preference)
                    if new_ip == "0.0.0.0":
                        # keep node_ip incase node_ip is a valid ip
                        self.missing_current_connection_ip[ip] = node
                    else:
                        node.node_ip = new_ip
                        # if no translation exists -> change public_ip/port back to None
                        # also need to change the publicIp
                        node.setNatIP(new_ip, self.nat)
                        self.retry_login_ips[new_ip] = node

        # sort nodes into passing, failed, missing list from retry_login_ips list
        def organizeNodes(self):
            # all nodes in retry_login_ips have failed through every preference
            self.failing_nodes.update(self.retry_login_ips)

            # go through missing_node_ip_list ips
            # valid node_ips go to failing_nodes
            # 0.0.0.0 ips stay in missing_node_ip_list
            for ip in list(self.missing_current_connection_ip.keys()):
                if self.missing_current_connection_ip[ip].node_ip != "0.0.0.0":
                    node = self.missing_current_connection_ip.pop(ip)
                    self.failing_nodes[node.node_ip] = node

        def getLoginSuccessNodes(self):
            return self.passing_nodes

        def getLoginFailedNodes(self):
            return self.failing_nodes

        def getMissingConnectionIps(self):
            return self.missing_current_connection_ip

class AsicType:
    UNKNOWN = 0
    MILLER = 3
    DONNER = 2
    SUGARBOWL = 4
    HOMEWOOD = 6
    HEAVENLY = 7
    WOLFRIDGE = 8
    ACI_Model_Catalog = {
        'N9K-M12PQ': MILLER,
        'N9K-C9396PX': DONNER,
        'N9K-M6PQ-E': DONNER,
        'N9K-M6PQ': DONNER,
        'N9K-C93128TX': DONNER,
        'N9K-C9396TX': DONNER,
        'N9K-C9372PX': DONNER,
        'N9K-C9372TX': DONNER,
        'N9K-C9332PQ': DONNER,
        'N9K-C9372PX-E': DONNER,
        'N9K-C93120TX': DONNER,
        'N9K-C9372TX-E': DONNER,
        'N9K-C93180YC-EX': SUGARBOWL,
        'N9K-93180YC-EX': SUGARBOWL,
        'N9K-C93108TC-EX': SUGARBOWL,
        'N9K-C93180LC-EX': SUGARBOWL,
        'N9K-C93108TC-FX': SUGARBOWL,
        'N9K-C93108YC-FX': SUGARBOWL,
        'N9K-C93180YC-FX': HOMEWOOD,
        'N9K-C9348GC-FXP': HOMEWOOD,
        'N9K-C9358GY-FXP': HOMEWOOD,
        'N9K-C9336C-FX': HEAVENLY,
        'N9K-C9336C-FX2': HEAVENLY,
        'N9K-C93216TC-FX2': HEAVENLY,
        'N9K-C93240YC-FX2': HEAVENLY,
        'N9K-C93360YC-FX2': HEAVENLY,
        'N9K-C9316D-GX': WOLFRIDGE,
        'N9K-C93600CD-GX': WOLFRIDGE,
        'N9K-C9364C-GX': WOLFRIDGE,
        'N9K-X9716D-GX': WOLFRIDGE,
        'N9K-C9504-FM-G': WOLFRIDGE,
        'N9K-C9508-FM-G': WOLFRIDGE,
    }

    @staticmethod
    def getAsicTypeFrmModelCatalog(model_name):
        if model_name in AsicType.ACI_Model_Catalog:
            return AsicType.ACI_Model_Catalog[model_name]
        else:
            return AsicType.UNKNOWN

    @staticmethod
    def getAsicTypeName(asic_value):
        if asic_value == AsicType.DONNER:
            return 'DONNER'
        elif asic_value == AsicType.MILLER:
            return 'MILLER'
        elif asic_value == AsicType.SUGARBOWL:
            return 'SUGARBOWL'
        elif asic_value == AsicType.HOMEWOOD:
            return 'HOMEWOOD'
        elif asic_value == AsicType.HEAVENLY:
            return 'HEAVENLY'
        elif asic_value == AsicType.WOLFRIDGE:
            return 'WOLFRIDGE'
        elif asic_value == AsicType.UNKNOWN:
            return 'UNKNOWN_ASICMODELTYPE'

# Keep enum in sync with ucs.proto


class QueryId:
    UNKNOWN_QUERY_ID = 0

    LOGICAL_FABRICNODE = 1
    LOGICAL_FABRICNODE_XML = 46
    LOGICAL_FABRICNODE_JSON = 47
    LOGICAL_FABRICLOOSENODE = 59
    LOGICAL_TOPSYSTEM_JSON = 43
    LOGICAL_TOPSYSTEM_XML = 44
    LOGICAL_TOPSYSTEM = 45
    LOGICAL_EQPTLC = 3
    LOGICAL_EQPTFC = 4
    LOGICAL_EQPTFCSLOT = 5
    LOGICAL_INFRACLUSTERPOL = 6
    LOGICAL_INFRAWINODE = 7
    LOGICAL_FVTENANT = 8
    LOGICAL_TENANT = 9   # Per tenant tree
    LOGICAL_FVLOCALE = 10
    LOGICAL_VLANCKTEP = 11
    LOGICAL_INFRAFUNCP = 12
    LOGICAL_MGMTNODEGRP = 13
    LOGICAL_EPMDYNEPGPOLICYTRIP = 14
    LOGICAL_BGPINSTPOL = 15
    LOGICAL_PHYSDOMP = 16
    LOGICAL_FVNSVLANINSTP = 17
    LOGICAL_INFRAATTENTITYP = 18
    LOGICAL_INFRAACCPORTGRP = 19
    LOGICAL_INFRAACCBNDLGRP = 20
    LOGICAL_INFRAACCPORTP = 21
    LOGICAL_INFRANODEP = 22
    LOGICAL_INFRAFEXP = 33
    LOGICAL_AUDITLOGS = 24
    LOGICAL_FAULTRECORDS = 25
    LOGICAL_EVENTLOGS = 26
    LOGICAL_APICVERSION = 27
    LOGICAL_SWITCHVERSION = 28
    LOGICAL_FABRICIPV4EXPG = 29
    LOGICAL_FABRICIPV6EXPG = 30
    LOGICAL_FABRICMACEXPG = 31
    LOGICAL_VXLANCKTEP = 32
    LOGICAL_MGMTRSOOBSTNODE = 34
    LOGICAL_MGMTRSOOBSTNODE_XML = 48
    LOGICAL_MGMTRSOOBSTNODE_JSON = 49
    LOGICAL_UNI_FABRIC = 35
    LOGICAL_UNI_INFRA = 36
    LOGICAL_FABRICPATHEP = 37
    LOGICAL_VMMPROVP = 38
    LOGICAL_L2EXTDOMP = 39
    LOGICAL_L3EXTDOMP = 40
    LOGICAL_VMMDOMP = 41
    LOGICAL_INFRACONT = 42
    LOGICAL_VNSVDEV = 51
    LOGICAL_CONFIG_EXPORT_POLICY = 53
    LOGICAL_CONFIG_EXPORT_POLICY_ID = 54
    LOGICAL_CONFIG_EXPORT_STATUS = 55
    LOGICAL_CONFIG_EXPORT_COPY = 56
    LOGICAL_CONFIG_EXPORT_DELETE_SNAPSHOT = 60
    LOGICAL_CONFIG_EXPORT_DELETE_JOB = 61

    LOGICAL_TIMESTAMP = 57
    LOGICAL_VZTOEPGANY = 58
    LOGICAL_LLDPCNTRLR = 62

    CONCRETE_DATE = 100
    CONCRETE_UPTIME = 101
    CONCRETE_LLDP = 102
    CONCRETE_EQPTSTATS = 103
    CONCRETE_OVERLAY = 104
    CONCRETE_VPC = 105
    CONCRETE_ISIS = 106
    CONCRETE_L3CTX = 107
    CONCRETE_IPV4INTF = 108
    CONCRETE_URIBV4 = 109
    CONCRETE_URIBV6 = 110
    CONCRETE_URIBV4_VSH = 144
    CONCRETE_URIBV6_VSH = 145
    CONCRETE_BGP = 112
    CONCRETE_EPMDB = 113
    CONCRETE_COOP_SESSIONS = 114
    CONCRETE_COOP_DB = 115
    CONCRETE_ACTRLRULE = 116
    CONCRETE_ACTRLFLT = 117
    CONCRETE_ACTRLSCOPE = 118
    CONCRETE_ACTRLENTRY = 119
    CONCRETE_ACTRLFVNWISSUES = 120
    CONCRETE_ACTRLRSTOEPGCONN = 121
    CONCRETE_ACTRLRULEHIT5MIN = 122
    CONCRETE_ACTRLRULEHIT1HOUR = 123
    CONCRETE_ACTRLRULEDESTGRP = 127
    CONCRETE_SVCREDIRDESTGRP = 128
    CONCRETE_SVCREDIRRSDESTATT = 129
    CONCRETE_SVCREDIRDEST = 130
    CONCRETE_OSPF = 131
    CONCRETE_OSPFV3 = 151
    CONCRETE_EIGRP = 132
    CONCRETE_LC = 133
    CONCRETE_FCSlot = 134
    CONCRETE_FC = 135
    CONCRETE_TOPSYSTEM = 136
    CONCRETE_SWITCHVERSION = 137
    CONCRETE_VLANCKTEP = 138
    CONCRETE_VXLANCKTEP = 139
    CONCRETE_EPMDYNEPGPOLICYTRIP = 140
    CONCRETE_ARP = 141
    CONCRETE_NETSTAT = 142
    CONCRETE_L1PHYSIF = 143
    CONCRETE_PC_SUMMARY = 147
    CONCRETE_PC_INTERNAL_INFO = 148
    CONCRETE_IPV6INTF = 149
    CONCRETE_VPC_BRIEF = 150

    HARDWARE_POLICY = 200  # Catch all for all hardware queries in policy universe
    HARDWARE_FIB = 201
    HARDWARE_FIB_SPINEFC = 202
    HARDWARE_FIB_V6 = 210
    HARDWARE_FIB_SPINEFC_V6 = 211
    HARDWARE_ELTMC = 203
    HARDWARE_LLDP_ENTRY = 204
    HARDWARE_CDP_ENTRY = 205
    HARDWARE_CDP_NEIGHBOR = 206
    HARDWARE_ELTMC_INTF = 207
    HARDWARE_ELTMC_VLAN_SUMMARY = 208
    HARDWARE_ELTMC_VLAN_BRIEF = 209

    VCENTER_VCENTER = 300

    NETSCALER_SYSTEM = 400
    NETSCALER_NETWORK = 401
    NETSCALER_LB = 402
    NETSCALER_GSLB = 403

    F5_SYSTEM = 500
    F5_NETWORK = 501
    F5_ARP = 502
    F5_POOL = 503
    F5_VLAN = 504
    F5_SELF_IP = 505
    F5_VIRTUAL = 506

    MSO_SITES = 600
    MSO_FABRIC_CONNECTIVITY = 601
    MSO_FABRIC_CONNECTIVITY_STATUS = 602
    MSO_SCHEMAS = 603
    MSO_TENANTS = 604
    MSO_POLICY_REPORT = 605

    #NXOS DCNM related Queries
    NX_FABRIC_DCNM_INVENTORY = 10000
    NX_FABRIC_DCNM_VERSION = 10001
    NX_FABRIC_DCNM_LINKS = 10002
    NX_FABRIC_DCNM_GLOBAL_INTERFACE = 10003

    #All NXOS switch related queries
    NX_FABRIC_SHOW_VERSION = 20000
    NX_FABRIC_VPC = 20001
    NX_FABRIC_VPC_BRIEF = 20002
    NX_FABRIC_VPC_CONSISTENCY_VLANS = 20003
    NX_FABRIC_NVE_INFRAVLAN = 20004
    NX_FABRIC_LACP = 20005
    NX_FABRIC_PHY_INTERFACE = 20006
    NX_FABRIC_PC_INTERFACE = 20007
    NX_FABRIC_SVI_INTERFACE = 20008
    NX_FABRIC_STP = 20009
    NX_FABRIC_ICMPV4 = 20010
    NX_FABRIC_ICMPV6 = 20011
    NX_FABRIC_IPV4 = 20012
    NX_FABRIC_IPV6 = 20013
    NX_FABRIC_PIM = 20014
    NX_FABRIC_OSPF = 20015
    NX_FABRIC_EPS = 20016
    NX_FABRIC_OSPF_NEIGHBORS = 20017
    NX_FABRIC_HMM = 20018
    NX_FABRIC_HSRP = 20019
    NX_FABRIC_ISIS_ADJACENCY = 20020
    NX_FABRIC_PIM_NEIGHBOR = 20021
    NX_FABRIC_L3INST = 20022
    NX_FABRIC_PIM_INTERFACE = 20023
    NX_FABRIC_PC_SUMMARY = 20024
    NX_FABRIC_VPC_CONSISTENCY_GLOBAL = 20025
    NX_FABRIC_VPC_CONSISTENCY_VNI = 20026
    NX_FABRIC_MAC_TABLE = 20027
    NX_FABRIC_SHOW_VXLAN = 20028
    NX_FABRIC_SHOW_IP_ARP_VRF = 20029
    NX_FABRIC_VRF_LIST = 20030
    NX_FABRIC_BD = 20031
    NX_FABRIC_SHOW_LLDP_NEIGHBORS = 20032
    NX_FABRIC_SHOW_IPV4_ROUTE = 20033
    NX_FABRIC_SHOW_IPV6_ROUTE = 20034
    NX_FABRIC_BGP = 20035
    NX_FABRIC_GET_SUPPORTED_FEATURE = 20036
    NX_FABRIC_SHOW_RUN_CONFIG = 20037
    NX_FABRIC_ISIS_INFO = 20038
    NX_FABRIC_LOOPBACK_INTF = 20039
    NX_FABRIC_VPC_CONSISTENCY_INTERFACE = 20040
    NX_FABRIC_L3INST_V2 = 20041
    NX_FABRIC_EVPN = 20042

    CUSTOM_COMMAND_BASE = 50000

class QueryIdToString:
    @staticmethod
    def getQueryName(queryid):
        for k in QueryId.__dict__:
            if QueryId.__dict__[k] == queryid:
                return k
        raise CandidDataCollectionException("Invalid queryid: " + str(queryid))

class FilterQueryIds:
    HARDWARE_MODEL_QUERY_IDS = [QueryId.CONCRETE_LC,
                                QueryId.CONCRETE_FCSlot,
                                QueryId.CONCRETE_FC,
                                QueryId.CONCRETE_SWITCHVERSION,
                                QueryId.CONCRETE_L1PHYSIF
                                ]
    TOPOLOGY_QUERY_IDS = [
        QueryId.LOGICAL_TIMESTAMP,
        QueryId.LOGICAL_TOPSYSTEM_XML,
        QueryId.LOGICAL_INFRACLUSTERPOL,
        QueryId.LOGICAL_INFRACONT,
        QueryId.LOGICAL_INFRAWINODE,
        QueryId.LOGICAL_APICVERSION,
        QueryId.LOGICAL_FABRICNODE_XML,
        QueryId.LOGICAL_SWITCHVERSION,
        QueryId.LOGICAL_MGMTRSOOBSTNODE_XML]

    CONFIG_EXPORT_QUERY_IDS = [
        QueryId.LOGICAL_CONFIG_EXPORT_POLICY,
        QueryId.LOGICAL_CONFIG_EXPORT_POLICY_ID,
        QueryId.LOGICAL_CONFIG_EXPORT_STATUS,
        QueryId.LOGICAL_CONFIG_EXPORT_COPY,
        QueryId.LOGICAL_CONFIG_EXPORT_DELETE_SNAPSHOT,
        QueryId.LOGICAL_CONFIG_EXPORT_DELETE_JOB]

    SUPPORTED_FEATURES_QUERY_IDS = [
        QueryId.NX_FABRIC_GET_SUPPORTED_FEATURE
    ]

    STANDALONE_TOPOLOGY_QUERY_IDS = []

    DCNM_TOPOLOGY_QUERY_IDS = []

    MSO_TOPOLOGY_QUERY_IDS = []

    @staticmethod
    def getTopologyQueryIdList():
        return FilterQueryIds.TOPOLOGY_QUERY_IDS

    @staticmethod
    def getHardwareModelQueryIds():
        return FilterQueryIds.HARDWARE_MODEL_QUERY_IDS

    @staticmethod
    def getTopologyExplorerQueryIds():
        return FilterQueryIds.getTopologyQueryIdList() \
               + FilterQueryIds.getHardwareModelQueryIds()\
               + FilterQueryIds.getStandaloneTopologyQueryIdList()

    @staticmethod
    def getConfigExportQueryIds():
        return FilterQueryIds.CONFIG_EXPORT_QUERY_IDS

    @staticmethod
    def getDcnmTopologyQueryIdList():
        return FilterQueryIds.DCNM_TOPOLOGY_QUERY_IDS

    @staticmethod
    def getStandaloneTopologyQueryIdList():
        return FilterQueryIds.STANDALONE_TOPOLOGY_QUERY_IDS

    @staticmethod
    def getSupportedFeaturesQueryIdList():
        return FilterQueryIds.SUPPORTED_FEATURES_QUERY_IDS

    @staticmethod
    def getMsoTopologyQueryIdList():
        return FilterQueryIds.MSO_TOPOLOGY_QUERY_IDS

'''
Query result stash to hold generic collector results
'''


class QueryResultsStash:

    def __init__(self):
        self.query_results = []

    def addQueryResult(self, result):
        self.query_results.append(result)

    '''
    Update list of results
    '''

    def addQueryResults(self, results):
        self.query_results.extend(results)

    '''
    Query can be either REST/SSH , filter by node_attr, value, query_id
    '''

    def lookupNodeQueries(
            self,
            query_id,
            node_attr_value,
            node_attr="node_id"):
        query_result = next((x for x in self.query_results if x.getQueryId() == query_id and
                             x.getNode().__dict__[node_attr] == node_attr_value
                             and x.getQueryStatus() == GenericQueryResult.QueryStatus.SUCCESS), None)
        if query_result:
            response = query_result.getQueryResponse()[0]
            return GlobalUtils.gzipDecompress(self, response)
        else:
            raise LookupError(
                "QueryId: %d  not present on node :%s " %
                (query_id, node_attr_value))

    def getQueryResults(self):
        return self.query_results


'''
Collection statistics result stash to hold generic collector stats
'''


class CollectionStatsStash:

    def __init__(self):
        self.node_collection_stats = []

    def addCollectionStat(self, result):
        self.node_collection_stats.append(result)

    def addCollectionStats(self, results):
        self.node_collection_stats.extend(results)

    def getCollectionStats(self, node_ip):
        stats = [x for x in self.node_collection_stats if x.node.getNodeIp() == node_ip]
        return stats


'''
Class to store results of GenericCollector
Mimics UCS query results
'''


class GenericQueryResult:
    class QueryType:
        UNKNOWN_QUERY_TYPE = 0
        REST = 1
        SSH = 2
        VCENTER = 3
        NETSCALER = 4
        SFTP = 5
        F5_LB = 6

    class QuerySubType:
        UNKNOWN_SUB_QUERY_TYPE = 0
        GET = 1
        POST = 2

    class QueryStatus:
        UNKNOWN_QUERY_STATUS = 0
        SUCCESS = 1
        FAIL = 2

    def __init__(self):
        self.query_type = self.QueryType.UNKNOWN_QUERY_TYPE
        self.query_status = self.QueryStatus.UNKNOWN_QUERY_STATUS
        self.query_id = QueryId.UNKNOWN_QUERY_ID
        self.node_info = None
        self.query = None
        self.query_response = None
        self.query_result_err = None
        self.query_time_millis = None
        self.query_param_remote_path = None
        self.query_param_tenant_name = None
        self.query_param_spine_fc = None
        self.query_response_size = 0
        self.query_response_time_millis = None
        self.legacy_query = False
        self.query_sub_type = self.QuerySubType.UNKNOWN_SUB_QUERY_TYPE
        self.query_data = None
        self.query_param_vrf_name = None
        self.query_param_vrf_count = None
        self.feature_set = None
        self.query_string = None

    def setQuerySubType(self, query_sub_type):
        self.query_sub_type = query_sub_type

    def getQuerySubType(self):
        return self.query_sub_type

    def setQueryId(self, query_id):
        self.query_id = query_id

    def getQueryId(self):
        return self.query_id

    def setNode(self, node):
        self.node_info = node

    def getNode(self):
        return self.node_info

    def setQueryCmd(self, cmd):
        self.query = cmd

    def getQueryCmd(self):
        return self.query

    def appendQueryCmd(self, cmd):
        if self.query:
            self.query = self.query + cmd

    def setQueryType(self, qtype):
        self.query_type = qtype

    def setLegacyQuery(self, legacy_query):
        self.legacy_query = legacy_query

    def isLegacyQuery(self):
        return self.legacy_query

    def setQueryStatus(self, status):
        self.query_status = status

    def getQueryType(self):
        return self.query_type

    def getQueryStatus(self):
        return self.query_status

    def getQueryStatusString(self):
        if self.query_status == self.QueryStatus.SUCCESS:
            return "SUCCESS"
        if self.query_status == self.QueryStatus.FAIL:
            return "FAIL"
        if self.query_status == self.QueryStatus.UNKNOWN_QUERY_STATUS:
            return "UNKNOWN_QUERY_STATUS"
        return None

    def setQueryResponse(self, rsp, err=None):
        self.query_response = rsp
        if err is not None:
            self.query_result_err = err

    def getQueryResponse(self):
        return (self.query_response, self.query_result_err)

    def setQueryResultError(self, err):
        self.query_result_err = err

    def setQueryTimeMillis(self, millis):
        self.query_time_millis = millis

    def getQueryTimeMillis(self):
        return self.query_time_millis

    def setQueryParamRemotePath(self, remote_path):
        self.query_param_remote_path = remote_path

    def getQueryParamRemotePath(self):
        return self.query_param_remote_path

    def setQueryParamTenantName(self, tenant_name):
        self.query_param_tenant_name = tenant_name
        return self

    def getQueryParamTenantName(self):
        return self.query_param_tenant_name

    def setQueryParamSpineFc(self, spine_fc):
        self.query_param_spine_fc = spine_fc
        return self

    def getQueryParamSpineFc(self):
        return self.query_param_spine_fc

    def setQueryResponseSize(self, size):
        self.query_response_size = size

    def getQueryResponseSize(self):
        return self.query_response_size

    def setQueryResponseTime(self, millis):
        self.query_response_time_millis = millis

    def getQueryResponseTime(self):
        return self.query_response_time_millis

    def isSuccess(self):
        return self.query_status == self.QueryStatus.SUCCESS

    def isFail(self):
        return self.query_status == self.QueryStatus.FAIL

    def isRest(self):
        return self.query_type == self.QueryType.REST

    def isSsh(self):
        return self.query_type == self.QueryType.SSH

    def isVCenter(self):
        return self.query_type == self.QueryType.VCENTER

    def isNetScaler(self):
        return self.query_type == self.QueryType.NETSCALER

    def setQueryData(self, data):
        self.query_data = data

    def getQueryData(self):
        return self.query_data

    def getQueryCmdWithoutZip(self, query_cmd):
        query_cmd_without_gzip = query_cmd.replace(' | gzip','')
        return query_cmd_without_gzip

    def getQueryCmdWithZip(self):
        query_cmd_with_gzip = self.query + ' | gzip'
        return query_cmd_with_gzip

    def setQueryParamVrfName(self, vrf_name):
        self.query_param_vrf_name = vrf_name
        return self

    def getQueryParamVrfName(self):
        return self.query_param_vrf_name

    def setQueryParamVrfCount(self, vrf_count):
        self.query_param_vrf_count = vrf_count
        return self

    def getQueryParamVrfCount(self):
        return self.query_param_vrf_count

    def setFeatureSet(self, features):
        if features:
            self.feature_set = features.split()
        return self

    def getFeatureSet(self):
        return self.feature_set

    def setQueryString(self, query_string):
        self.query_string = query_string

    def getQueryString(self):
        return self.query_string


def RestQuery(query_id, query_cmd=None, legacy_query=False,
              query_sub_type=GenericQueryResult.QuerySubType.GET,
              query_data=None, standalone=False, features=None):
    query = GenericQueryResult()
    query.setQueryId(query_id)
    if query_cmd:
        query.setQueryCmd(query_cmd)
    query.setLegacyQuery(legacy_query)
    query.setQueryType(GenericQueryResult.QueryType.REST)
    query.setQuerySubType(query_sub_type)
    if query_data and query_sub_type == GenericQueryResult.QuerySubType.POST:
        query.setQueryData(query_data)

    if features:
        query.setFeatureSet(features)
    return query

'''
ACI standard command-line interface is iBash (Bash prompt plus custom ACI cmds)
Example ACI ssh query,
--> "vsh -c 'show version'"

NXOS standard command-line interface is vsh (The shell that understands switch cmds)
Example NXOS ssh query,
--> "show version"
'''
def SshQuery(query_id, query_cmd, legacy_query=False, standalone=False, features=None):
    query_cmd = query_cmd if standalone else "timeout 1m " + query_cmd
    query = GenericQueryResult()
    query.setQueryId(query_id)
    query.setQueryCmd(query_cmd)
    query.setLegacyQuery(legacy_query)
    query.setQueryType(GenericQueryResult.QueryType.SSH)
    if features:
        query.setFeatureSet(features)
    return query


def VCenterQuery(query_id, query_cmd, legacy_query=False):
    query = GenericQueryResult()
    query.setQueryId(query_id)
    query.setQueryCmd(query_cmd)
    query.setLegacyQuery(legacy_query)
    query.setQueryType(GenericQueryResult.QueryType.VCENTER)
    return query

# RemotePath for SFTP is stored as a param
def SFTPQuery(query_id, legacy_query=False):
    query = GenericQueryResult()
    query.setQueryId(query_id)
    query.setQueryCmd("sftp ")
    query.setLegacyQuery(legacy_query)
    query.setQueryType(GenericQueryResult.QueryType.SFTP)
    return query

def NetScalerQuery(query_id, query_cmd, legacy_query=False):
    query = GenericQueryResult()
    query.setQueryId(query_id)
    query.setQueryCmd(query_cmd)
    query.setLegacyQuery(legacy_query)
    query.setQueryType(GenericQueryResult.QueryType.NETSCALER)
    return query

def F5Query(query_id, query_cmd, legacy_query=False):
    query = GenericQueryResult()
    query.setQueryId(query_id)
    query.setQueryCmd(query_cmd)
    query.setLegacyQuery(legacy_query)
    query.setQueryType(GenericQueryResult.QueryType.F5_LB)
    return query

class NodeCollectionStats:

    def __init__(self, logger, node, total_query_count, current_time):
        self.logger = logger
        self.node = node
        self.rest_login = False
        self.ssh_login = False
        self.vcenter_login = False
        self.netscaler_login = False
        self.reachable = False
        self.total_query_count = total_query_count
        self.failed_query_info = []
        self.failed_query_count = 0
        self.current_collection_time = 0
        self.collection_time = 0
        self.collection_start_time = current_time

    def __str__(self):
        return (
            "ping_test: %s rest_login: %s ssh_login: %s vcenter_login: %s netscaler_login: %s "
            "total_query_count: %d failed_query_count: %d collection_time: %ds" %
            (self.reachable,
             self.rest_login,
             self.ssh_login,
             self.vcenter_login,
             self.netscaler_login,
             self.total_query_count,
             self.failed_query_count,
             self.collection_time))

    def setCollectionStartTime(self, time):
        self.collection_start_time = time

    def getCollectionStartTime(self):
        return self.collection_start_time

    def setRestLogin(self, login_status):
        self.rest_login = login_status

    def getRestLogin(self):
        return self.rest_login

    def setReachable(self, reachable):
        self.reachable = reachable

    def getNode(self):
        return self.node

    def setNode(self, node):
        self.node = node

    def getReachable(self):
        return self.reachable

    def setSshLogin(self, login_status):
        self.ssh_login = login_status

    def getSshLogin(self):
        return self.ssh_login

    def setVCenterLogin(self, login_status):
        self.vcenter_login = login_status

    def getVCenterLogin(self):
        return self.vcenter_login

    def setNetScalerLogin(self, login_status):
        self.netscaler_login = login_status

    def getNetScalerLogin(self):
        return self.netscaler_login

    def setF5Login(self, login_status):
        self.f5_login = login_status

    def getF5Login(self):
        return self.f5_login

    def setTotalQueryCount(self, total_query_count):
        self.total_query_count = total_query_count

    def getTotalQueryCount(self):
        return self.total_query_count

    def setFailedQuery(self, query):
        query_failure_reason = ''
        if query.getQueryStatus() == GenericQueryResult.QueryStatus.FAIL:
            self.failed_query_count = self.failed_query_count + 1
            (rsp, err) = query.getQueryResponse()
            # In case of rest, rsp has error msg, in case of ssh stderr has the
            # error reason
            if query.isRest() and rsp:
                query_failure_reason = zlib.decompress(
                    rsp, zlib.MAX_WBITS | 32)
            elif query.isSsh() and err:
                query_failure_reason = zlib.decompress(
                    err, zlib.MAX_WBITS | 32)
            elif query.isVCenter() and err:
                query_failure_reason = err
            elif query.isNetScaler() and err:
                query_failure_reason = err

            self.failed_query_info.append(
                (query.getQueryCmd(), query_failure_reason))

    def getFailedQueryCount(self):
        return self.failed_query_count

    def getFailedQueryInfo(self):
        return self.failed_query_info

    def setCollectionTime(self, collection_time):
        self.collection_time = int(collection_time)

    def getCollectionTime(self):
        return self.collection_time


class GenericCollectorNodePartitioner:

    def __init__(
            self,
            partition_index,
            partition_count,
            optimized_partition,
            nodes,
            logger):
        self.partition_index = partition_index
        self.partition_count = partition_count
        self.optimized_partition = optimized_partition
        self.nodes = nodes
        self.logger = logger
        self.partition_nodes = []
        self.partitionNodes()

    def partitionNodes(self):
        sorted_nodes = []
        apic_nodes = [x for x in self.nodes if x.isController()]
        leaf_nodes = [x for x in self.nodes if x.isLeaf()]
        spine_nodes = [x for x in self.nodes if x.isSpine()]
        dcnm_nodes = [x for x in self.nodes if x.isDcnm()]
        mso_nodes = [x for x in self.nodes if x.isMso()]
        standalone_spine_nodes = [x for x in self.nodes if x.isStandaloneSpine()]
        standalone_leaf_nodes = [x for x in self.nodes if x.isStandaloneLeaf()]
        vcenter_nodes = [x for x in self.nodes if x.isVCenter()]
        netscaler_nodes = [x for x in self.nodes if x.isNetScaler()]
        f5_nodes = [x for x in self.nodes if x.isF5()]
        sorted_nodes.extend(apic_nodes)
        sorted_nodes.extend(leaf_nodes)
        sorted_nodes.extend(spine_nodes)
        sorted_nodes.extend(vcenter_nodes)
        sorted_nodes.extend(netscaler_nodes)
        sorted_nodes.extend(f5_nodes)
        sorted_nodes.extend(dcnm_nodes)
        sorted_nodes.extend(mso_nodes)
        sorted_nodes.extend(standalone_leaf_nodes)
        sorted_nodes.extend(standalone_spine_nodes)

        # Optimize partitioning if num_partitions > 1 and optimize_partition
        # flag is set
        if self.optimized_partition and self.partition_count > 1:
            # nth parition is reserved for controllers
            # Total partitions is n, last partition is n-1
            if self.partition_index == self.partition_count - 1:
                for i, each_topo_node in enumerate(apic_nodes):
                    node_id = each_topo_node.node_id
                    self.partition_nodes.append(each_topo_node)
                    self.logger.info(
                        "Collecting information for partition: %d,node :%d role:%s" %
                        (self.partition_index, node_id, each_topo_node.node_role))
            else:
                other_nodes = leaf_nodes + spine_nodes + vcenter_nodes + \
                              netscaler_nodes + f5_nodes + \
                              standalone_spine_nodes + standalone_leaf_nodes
                for i, each_topo_node in enumerate(other_nodes):
                    node_id = each_topo_node.node_id
                    if self.partition_index == i % (self.partition_count - 1):
                        self.partition_nodes.append(each_topo_node)
                        self.logger.info(
                            "Collecting information for partition: %d,node :%d role:%s" %
                            (self.partition_index, node_id, each_topo_node.node_role))
        else:
            for i, each_topo_node in enumerate(sorted_nodes):
                node_id = each_topo_node.node_id
                if self.partition_index == i % self.partition_count:
                    self.partition_nodes.append(each_topo_node)
                    self.logger.info(
                        "Collecting information for partition: %d,node :%d role:%s" %
                        (self.partition_index, node_id, each_topo_node.node_role))

    def getPartitionedNodes(self):
        return self.partition_nodes


'''
Generic collector design , given node, uri/ssh , collects data from the node
'''


class GenericCollector:

    class LogicalQueries:
        class ApicConfigExportPolicy:
            export_policy = Template('<fabricInst dn="uni/fabric">\
                            <configExportP name=$export_name snapshot="yes" format=$export_format includeSecureFields="no" adminSt="triggered">\
                               <configRsExportDestination tnFileRemotePathName="localhost" />\
                            </configExportP>\
                            </fabricInst>')
            remote_path = '/data2/snapshots/'
            export_policy_dn = Template('uni/fabric/configexp-$export_name')
            config_job_dn = Template(
                'uni/backupst/jobs-[$export_dn]/run-$run_time')
            snapshot_job_dn = Template(
                'uni/backupst/snapshots-[$export_dn]/snapshot-run-$run_time')
            config_job_cont_dn = Template('uni/backupst/jobs-[$export_dn]')
            delete_snapshot = Template('<configSnapshot dn="$snapshot_job_dn" retire="yes"/>')
            delete_config_job = Template('<configExportP dn="$export_policy_dn" status="deleted"> </configExportP>')

            @staticmethod
            def getRemotePath(cls):
                return cls.LogicalQueries.ApicConfigExportPolicy.remote_path

            @staticmethod
            def getPolicyTemplate(cls):
                return cls.LogicalQueries.ApicConfigExportPolicy.export_policy

            @staticmethod
            def getExportDnTemplate(cls):
                return cls.LogicalQueries.ApicConfigExportPolicy.export_policy_dn

            @staticmethod
            def getConfigJobDnTemplate(cls):
                return cls.LogicalQueries.ApicConfigExportPolicy.config_job_dn

            @staticmethod
            def getSnapshotJobDnTemplate(cls):
                return cls.LogicalQueries.ApicConfigExportPolicy.snapshot_job_dn

            @staticmethod
            def getConfigJobContDnTemplate(cls):
                return cls.LogicalQueries.ApicConfigExportPolicy.config_job_cont_dn

            @staticmethod
            def getDeleteSnapshotTemplate(cls):
                return cls.LogicalQueries.ApicConfigExportPolicy.delete_snapshot

            @staticmethod
            def getDeleteExportConfigTemplate(cls):
                return cls.LogicalQueries.ApicConfigExportPolicy.delete_config_job

        class TenantSubTreeClassName:
            ctx_tree = 'fvCtx,vzAny,vzRsAnyToProv,vzRsAnyToCons,vzRsAnyToConsIf,fvRtCtx,'
            epg_tree = 'fvAp,fvAEPg,fvRsDomAtt,fvRsBd,fvRsCons,fvRsProv,fvRsProtBy,' +\
                'fvRsConsIf,fvRsPathAtt,fvRsNodeAtt,fvStCEp,fvStIp,fvCEp,fvRsStCEpToPathEp,' +\
                'fvSubnet,vnsAEPpInfo,'
            bd_tree = 'fvBD,fvRtBd,fvRsCtx,fvSubnet,fvRsBDToOut,fvRsBDSubnetToProfile,dhcpLbl,fvRsBdToEpRet,'
            l3ext_tree = 'l3extOut,l3extRsNodeL3OutAtt,ipRouteP,ipNexthopP,' +\
                'l3extRsPathL3OutAtt,l3extSubnet,l3extRsEctx,l3extInstP,ospfExtP,bgpExtP,eigrpExtP,l3extConsLbl,l3extProvLbl,l3extLNodeP,' +\
                'l3extLIfP,l3extMember,l3extExtEncapAllocator,l3extLoopBackIfP,rtctrlProfile,'
            l2ext_tree = 'l2extOut,l2extRsEBd,l2extInstP,l2extRsPathL2OutAtt,'
            vzbrcp_tree = 'vzBrCP,vzSubj,vzRsSubjFiltAtt,vzRsFiltAtt,' +\
                'vzRtCons,vzRtProv,vzRtAnyToProv,vzRtAnyToCons,vzRsIf,vzRsSubjGraphAtt,'
            vzbrcpif_tree = 'vzCPIf,vzRtIf,vzIntDef,vzRtConsIf,vzRtAnyToConsIf,'
            vz_filter_tree = 'vzFilter,vzEntry,vzRFltP,vzRFltE,vzERFltP,'
            vz_taboo_tree = 'vzTaboo,vzTSubj,vzRsDenyRule,vzRtProtBy,'
            service_graph_tree = 'vnsLDevInst,vnsGraphInst,vnsAbsGraph,vnsAbsNode,vnsInTerm,vnsOutTerm,' +\
                'vnsFltInst,vnsNodeInst,vnsTermNodeInst,vnsFuncConnInst,vnsTermConnInst,vnsRsEPpInfoToBD,' +\
                'vnsConnectionInst,vnsRsConnectionInstConns,vnsRsEPgDefToConn,vnsRsTermInstMeta,' +\
                'vnsRsEPpInfoAtt,vnsRsLDevInst,vnsSvcCont,vnsSvcRedirectPol,vnsLDevCtx,vnsLIfCtx,' +\
                'vnsRsLIfCtxToSvcRedirectPol,vnsRsNodeInstToLDevCtx,vnsRsTermToEPg,vnsRsTermToAny,' +\
                'vnsRsConnToFltInst,vnsLDevVip,vnsLIf,vnsCDev,vnsCIf,vnsRsALDevToPhysDomP,vnsRsALDevToDomP,' +\
                'vnsRsLDevCtxToLDev,vnsRsLIfCtxToBD,vnsRedirectDest,vnsRsLIfCtxToLIf,'
            addr_tree = 'fvnsAddrInst,fvnsRtAddrInst,fvnsUcastAddrBlk,'
            misc_tree = 'fvConnInstrPol,vzOOBBrCP,fvEpRetPol,pimExtP,rtctrlAttrP,rtctrlSubjP'

            subtree_class_filter = epg_tree + bd_tree + ctx_tree + l3ext_tree +\
                l2ext_tree + vzbrcp_tree + vzbrcpif_tree +\
                vz_filter_tree + vz_taboo_tree + service_graph_tree +\
                addr_tree + misc_tree

        @staticmethod
        def getTopologyApicQueries():
            all_apic_queries = [
                RestQuery(QueryId.LOGICAL_FABRICNODE_JSON, "/api/class/fabricNode.json"),
                RestQuery(QueryId.LOGICAL_TOPSYSTEM_JSON, "/api/class/topSystem.json"),
                RestQuery(QueryId.LOGICAL_MGMTRSOOBSTNODE_JSON, "/api/class/mgmtRsOoBStNode.json"),
                RestQuery(QueryId.LOGICAL_EQPTLC, "/api/class/eqptLC.json"),
                RestQuery(QueryId.LOGICAL_EQPTFCSLOT, "/api/class/eqptFCSlot.json"),
                RestQuery(QueryId.LOGICAL_EQPTFC, "/api/class/eqptFC.json"),


                RestQuery(QueryId.LOGICAL_TIMESTAMP, "/api/mo/info.xml"),
                RestQuery(QueryId.LOGICAL_FABRICNODE_XML, "/api/class/fabricNode.xml"),
                RestQuery(QueryId.LOGICAL_TOPSYSTEM_XML, "/api/class/topSystem.xml"),
                RestQuery(QueryId.LOGICAL_MGMTRSOOBSTNODE_XML, "/api/class/mgmtRsOoBStNode.xml"),
                RestQuery(QueryId.LOGICAL_EQPTLC, "/api/class/eqptLC.xml"),
                RestQuery(QueryId.LOGICAL_EQPTFCSLOT, "/api/class/eqptFCSlot.xml"),
                RestQuery(QueryId.LOGICAL_EQPTFC, "/api/class/eqptFC.xml"),
                RestQuery(QueryId.LOGICAL_INFRACLUSTERPOL, "/api/class/infraClusterPol.xml"),
                RestQuery(QueryId.LOGICAL_INFRAWINODE, "/api/class/infraWiNode.xml"),
                RestQuery(QueryId.LOGICAL_INFRACONT, "/api/class/infraCont.xml"),
                RestQuery(QueryId.LOGICAL_APICVERSION, "/api/class/firmwareCtrlrRunning.json"),
                RestQuery(QueryId.LOGICAL_SWITCHVERSION, "/api/class/firmwareRunning.json"),
            ]
            return all_apic_queries

        @staticmethod
        def getApicQueries(cls):
            uniFabricQuery = "/api/mo/uni/fabric.json?rsp-subtree=full"
            uniFabricClasses = "fabricRsOosPath,fabricLocale"

            uniInfraQuery = "/api/mo/uni/infra.json?rsp-subtree=full"
            uniInfraClasses = "infraNodeP,infraLeafS,infraRsAccPortP,infraNodeBlk,infraRsAccNodePGrp,infraAccPortP,infraHPortS,infraPortBlk,infraRsAccBaseGrp,lldpIfPol,cdpIfPol"

            if (cls.optimized_query):
                uniFabricQuery = uniFabricQuery + "&rsp-subtree-class=" + uniFabricClasses
                uniInfraQuery = uniInfraQuery + "&rsp-subtree-class=" + uniInfraClasses

            apic_queries = [
                RestQuery(QueryId.LOGICAL_TOPSYSTEM, "/api/class/topSystem.json"),
                RestQuery(QueryId.LOGICAL_FVTENANT, "/api/class/fvTenant.json"),
                RestQuery(QueryId.LOGICAL_UNI_FABRIC, uniFabricQuery),
                RestQuery(QueryId.LOGICAL_UNI_INFRA, uniInfraQuery),
                RestQuery(QueryId.LOGICAL_PHYSDOMP, "/api/class/physDomP.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_VMMPROVP, "/api/class/vmmProvP.json"),
                RestQuery(QueryId.LOGICAL_VMMDOMP, "/api/class/vmmDomP.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_L2EXTDOMP, "/api/class/l2extDomP.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_L3EXTDOMP, "/api/class/l3extDomP.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_FABRICPATHEP, "/api/class/fabricPathEpCont.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_FVNSVLANINSTP, "/api/class/fvnsVlanInstP.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_INFRAATTENTITYP, "/api/class/infraAttEntityP.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_INFRAACCPORTGRP, "/api/class/infraAccPortGrp.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_INFRAACCBNDLGRP, "/api/class/infraAccBndlGrp.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_INFRAACCPORTP, "/api/class/infraAccPortP.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_INFRANODEP, "/api/class/infraNodeP.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_INFRAFEXP, "/api/class/infraFexP.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_BGPINSTPOL, "/api/class/bgpInstPol.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_FABRICLOOSENODE, "/api/class/fabricLooseNode.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_FVLOCALE, "/api/class/fvLocale.json"),
                RestQuery(QueryId.LOGICAL_INFRAFUNCP, "/api/class/infraFuncP.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_MGMTNODEGRP, "/api/class/mgmtNodeGrp.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_FABRICIPV4EXPG, "/api/class/fabricIPV4ExpG.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_FABRICIPV6EXPG, "/api/class/fabricIPV6ExpG.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_FABRICMACEXPG, "/api/class/fabricMacExpG.json?rsp-subtree=full"),
                RestQuery(QueryId.LOGICAL_EPMDYNEPGPOLICYTRIP,
                          "/api/class/epmDynEpgPolicyTrig.json", legacy_query=True),
                RestQuery(QueryId.LOGICAL_VLANCKTEP,
                          "/api/class/vlanCktEp.json", legacy_query=True),
                RestQuery(QueryId.LOGICAL_VXLANCKTEP,
                          "/api/class/vxlanCktEp.json", legacy_query=True),
                RestQuery(QueryId.LOGICAL_VNSVDEV, "/api/class/vnsVDev.json?rsp-subtree=full"),
                # RestQuery(QueryId.LOGICAL_AUDITLOGS, "/api/node/class/aaaModLR.json"),
                RestQuery(QueryId.LOGICAL_CONFIG_EXPORT_POLICY,
                          "/api/mo/uni/fabric.xml",
                          query_sub_type=GenericQueryResult.QuerySubType.POST),
                # QueryCmd is calculated at run-time
                RestQuery(QueryId.LOGICAL_CONFIG_EXPORT_POLICY_ID),
                RestQuery(QueryId.LOGICAL_CONFIG_EXPORT_STATUS),
                SFTPQuery(QueryId.LOGICAL_CONFIG_EXPORT_COPY),
                RestQuery(QueryId.LOGICAL_CONFIG_EXPORT_DELETE_SNAPSHOT,
                          query_sub_type=GenericQueryResult.QuerySubType.POST),
                RestQuery(QueryId.LOGICAL_CONFIG_EXPORT_DELETE_JOB,
                          query_sub_type=GenericQueryResult.QuerySubType.POST),
                RestQuery(QueryId.LOGICAL_VZTOEPGANY, "/api/class/vzToEPgAny.json"),
                RestQuery(QueryId.LOGICAL_LLDPCNTRLR, "/api/class/lldpCtrlrAdjEp.json?rsp-subtree=full")
            ]
            return apic_queries

        @staticmethod
        def getTenantList(cls, node):
            cls.logger.info(
                "Collecting per tenant query information from node:%s ip:%s role:%s" %
                (node.node_name, node.getNodeIp(), node.node_role))
            tenants = []
            rest_access = None
            try:
                apic_url = cls.create_base_url(cls.protocol, node.getNodeIp(), cls.port)
                login_time_out , query_time_out, node_time_out  = cls.getNodeTimeOut(node)
                session = LoginSession(apic_url, cls.user, cls.password, timeout=(
                    login_time_out, query_time_out), request_format='json')
                rest_access = DirectRestAccess(session)
                rest_access.login()
                tenants = rest_access.query(ClassQuery('fvTenant'))['imdata']
            except Exception as e:
                cls.logger.warning("Tenant lookup failed, Reason :%s" % str(e))
            else:
                tenants = sorted(
                    tenants, key=lambda k: k['fvTenant']['attributes']['name'])
            finally:
                if rest_access is not None:
                    try:
                        rest_access.logout()
                    except Exception as e:
                        cls.logger.warning("logout failed due to: %s"%str(e))
            return tenants

        @staticmethod
        def getPerTenantQueries(cls, node):
            per_tenant_queries = []
            tenants = cls.LogicalQueries.getTenantList(cls, node)
            for each_tenant in tenants:
                tenant_name = each_tenant['fvTenant']['attributes']['name']
                # TODO: make it backward compatible
                tenant_query = '/api/mo/uni/tn-' + tenant_name + '.json?rsp-subtree=full'
                if (tenant_name != 'mgmt') and (
                        tenant_name != 'infra') and cls.optimized_query:
                    sub_tree_class_filter = cls.LogicalQueries.TenantSubTreeClassName.subtree_class_filter
                    tenant_query += "&rsp-subtree-class=" + sub_tree_class_filter
                per_tenant_queries.append(
                    RestQuery(
                        QueryId.LOGICAL_TENANT,
                        tenant_query).setQueryParamTenantName(tenant_name))
            return per_tenant_queries



        @staticmethod
        def createAuditQuery(logger, timestamp):
            if timestamp == None:
                logger.debug("No timestamp to create Audit Log Query")
                return None;

            try:
                # timestamp format is <date>T<time><timezone>
                timezone_beginning_idx = max(timestamp.rfind("-"), timestamp.rfind("+"))
                if timezone_beginning_idx < timestamp.find("T"):
                    timezone_beginning_idx = len(timestamp)
                timezone = timestamp[timezone_beginning_idx:]
                modified_timestamp = timestamp[:timezone_beginning_idx]
                time_format = "%Y-%m-%dT%H:%M:%S.%f"
                today = datetime.datetime.strptime(modified_timestamp, time_format)
                yesterday = today - datetime.timedelta(
                            hours=AUDIT_LOG_ELAPSED_HISTORY_HOURS)
            except Exception as e:
                logger.error("Calculating Audit Log Query from" + \
                             " {0} failed due to: {1}".format(
                                    timestamp, str(e)))
                return None

            base = '(aaaModLR.created,"{0}{1}")'
            lt = "lt" + base.format(today.strftime(time_format), timezone)
            ge = "ge" + base.format(yesterday.strftime(time_format), timezone)
            query = "/api/node/class/aaaModLR.json?query-target-filter=and({0},{1})".format(
                        ge,lt).replace("+","%2B")
            return RestQuery(QueryId.LOGICAL_AUDITLOGS, query)

    class SwitchQueries:

        @staticmethod
        def getQueries(
                cls,
                asic_type,
                node_role,
                node_fcs=None,
                node_intf_list=None):
            # NOTE: Queries will be executed in order they are specified here
            # Routing configs
            queries = [
                SshQuery(QueryId.CONCRETE_DATE, 'date +%s'),
                SshQuery(QueryId.CONCRETE_UPTIME, 'cat /proc/uptime'),
                RestQuery(QueryId.CONCRETE_TOPSYSTEM, '/api/mo/sys.json?rsp-subtree=full&rsp-subtree-class=l1PhysIf,pcAggrIf,vpcIf',
                          legacy_query=True),
                RestQuery(QueryId.CONCRETE_TOPSYSTEM, '/api/mo/sys.json?rsp-subtree=full&rsp-subtree-class=l1PhysIf,ethpmPhysIf',
                          legacy_query=True),
                RestQuery(QueryId.CONCRETE_TOPSYSTEM, '/api/mo/sys.json?rsp-subtree=full&rsp-subtree-class=l1PhysIf,pcAggrIf,vpcIf,tunnelIf'),
                RestQuery(QueryId.CONCRETE_LLDP, '/api/mo/sys/lldp/inst.json?query-target=subtree&target-subtree-class=lldpAdjEp'),
                RestQuery(QueryId.CONCRETE_EQPTSTATS, '/api/mo/sys.json?query-target=subtree&rsp-subtree-class=eqptIngrTotal5min,eqptEgrTotal5min&rsp-subtree-include=stats,no-scoped'),
                RestQuery(QueryId.CONCRETE_OVERLAY, '/api/mo/sys/ipv4/inst/dom-overlay-1.json'),
                RestQuery(QueryId.CONCRETE_VPC, '/api/mo/sys/vpc/inst.json?query-target=subtree&rsp-subtree=full&query-target=subtree&target-subtree-class=vpcDom'),
                RestQuery(QueryId.CONCRETE_ISIS, '/api/mo/sys/isis/inst-default/dom-overlay-1/lvl-l1/db-dtep.json?rsp-subtree=full'),
                RestQuery(QueryId.CONCRETE_BGP, '/api/mo/sys/bgp.json?rsp-subtree=full&rsp-subtree-class=bgpRttP,bgpPeerEntry,bgpRoute'),
                RestQuery(QueryId.CONCRETE_L3CTX, '/api/mo/sys.json?rsp-subtree=full&rsp-subtree-class=l3Ctx,l3Inst,l2BD,vlanCktEp,l2RsPathDomAtt&query-target=subtree&target-subtree-class=l3Ctx,l3Inst'),
                SshQuery(QueryId.CONCRETE_PC_SUMMARY, "vsh -c 'show port-channel summary'"),
                SshQuery(QueryId.CONCRETE_PC_INTERNAL_INFO, "vsh -c 'show port-channel internal info all'"),
                SshQuery(QueryId.CONCRETE_VPC_BRIEF, "vsh -c 'show vpc brief'"),
                RestQuery(QueryId.CONCRETE_IPV4INTF, '/api/mo/sys/ipv4/inst.json?rsp-subtree=full&rsp-subtree-class=ipv4Dom,ipv4If,ipv4Addr&query-target=subtree&target-subtree-class=ipv4Inst'),
                RestQuery(QueryId.CONCRETE_IPV6INTF, '/api/mo/sys/ipv6/inst.json?rsp-subtree=full&rsp-subtree-class=ipv6Dom,ipv6If,ipv4Addr&query-target=subtree&target-subtree-class=ipv6Inst'),
                RestQuery(QueryId.CONCRETE_OSPF, '/api/mo/sys/ospf.json?rsp-subtree=full&rsp-subtree-class=ospfRoute,ospfIf'),
                RestQuery(QueryId.CONCRETE_OSPFV3, '/api/mo/sys/ospfv3.json?rsp-subtree=full&rsp-subtree-class=ospfv3Route,ospfv3If'),
                RestQuery(QueryId.CONCRETE_EIGRP, '/api/mo/sys/eigrp.json?rsp-subtree=full&rsp-subtree-class=eigrpRoute'),
                RestQuery(QueryId.CONCRETE_SWITCHVERSION, '/api/class/firmwareRunning.json'),
                RestQuery(QueryId.CONCRETE_ARP, '/api/mo/sys/arp.json?rsp-subtree=full'),
                SshQuery(QueryId.CONCRETE_NETSTAT, 'netstat -rn')
            ]
            # RIB / FIB
            queries.append(
                RestQuery(
                    QueryId.CONCRETE_URIBV4,
                    '/api/mo/sys/uribv4.json?rsp-subtree=full'))
            queries.append(
                RestQuery(
                    QueryId.CONCRETE_URIBV6,
                    '/api/mo/sys/uribv6.json?rsp-subtree=full'))
            queries.append(
                SshQuery(
                    QueryId.CONCRETE_URIBV4_VSH,
                    "vsh -c 'show ip route detail vrf all'"))
            queries.append(
                SshQuery(
                    QueryId.CONCRETE_URIBV6_VSH,
                    "vsh -c 'show ipv6 route detail vrf all'"))
            queries.extend(
                cls.SwitchQueries.getFibQueries(
                    node_role, node_fcs))
            # EP DBs
            queries.append(
                RestQuery(
                    QueryId.CONCRETE_EPMDB,
                    '/api/mo/sys.json?rsp-subtree=full&rsp-subtree-class=l2BD,vlanCktEp,vxlanCktEp,epmDb,epmMacEp,epmIpEp&query-target=subtree&target-subtree-class=l3Ctx'))
            if node_role == LEAF:
                queries.append(
                    RestQuery(
                        QueryId.CONCRETE_VLANCKTEP,
                        '/api/class/vlanCktEp.json?rsp-subtree=children&rsp-subtree-class=l2RsPathDomAtt')),
                queries.append(
                    RestQuery(
                        QueryId.CONCRETE_VXLANCKTEP,
                        '/api/class/vxlanCktEp.json')),
                queries.append(
                    RestQuery(
                        QueryId.CONCRETE_EPMDYNEPGPOLICYTRIP,
                        '/api/class/epmDynEpgPolicyTrig.json')),
                queries.append(
                    RestQuery(
                        QueryId.CONCRETE_COOP_SESSIONS,
                        '/api/mo/sys/coop/inst/dom-overlay-1.json?query-target=children'))
            elif node_role == SPINE:
                queries.append(
                    RestQuery(
                        QueryId.CONCRETE_COOP_DB,
                        '/api/mo/sys/coop/inst/dom-overlay-1/db-ep.json?rsp-subtree=full'))
            # Policy and faults
            if node_role == LEAF:
                queries.extend([
                    RestQuery(QueryId.CONCRETE_ACTRLRSTOEPGCONN, '/api/node/class/actrlRsToEpgConn.json'),
                    RestQuery(QueryId.CONCRETE_ACTRLRULE, '/api/node/class/actrlRule.json'),
                    RestQuery(QueryId.CONCRETE_ACTRLRULEDESTGRP, '/api/node/class/actrlRsToRedirDestGrp.json'),
                    RestQuery(QueryId.CONCRETE_SVCREDIRDESTGRP, '/api/node/class/svcredirDestGrp.json'),
                    RestQuery(QueryId.CONCRETE_SVCREDIRRSDESTATT, '/api/node/class/svcredirRsDestAtt.json'),
                    RestQuery(QueryId.CONCRETE_SVCREDIRDEST, '/api/node/class/svcredirDest.json'),
                    RestQuery(QueryId.CONCRETE_ACTRLFLT, '/api/node/class/actrlFlt.json'),
                    RestQuery(QueryId.CONCRETE_ACTRLSCOPE, '/api/node/class/actrlScope.json'),
                    RestQuery(QueryId.CONCRETE_ACTRLENTRY, '/api/node/class/actrlEntry.json'),
                    RestQuery(QueryId.CONCRETE_ACTRLFVNWISSUES, '/api/node/class/fvNwIssues.json'),
                    RestQuery(QueryId.CONCRETE_ACTRLRULEHIT5MIN, '/api/node/class/actrlRuleHit5min.json'),
                    RestQuery(QueryId.CONCRETE_ACTRLRULEHIT1HOUR, '/api/node/class/actrlRuleHit1h.json'),
                    RestQuery(QueryId.CONCRETE_LC, '/api/class/eqptLC.xml'),
                    RestQuery(QueryId.CONCRETE_L1PHYSIF, '/api/node/class/l1PhysIf.xml'),
                ])
                for cmd in cls.SwitchQueries.getASICCmds(cls, asic_type):
                    queries.append(SshQuery(QueryId.HARDWARE_POLICY, cmd))
            elif node_role == SPINE:
                queries.extend([
                    RestQuery(QueryId.CONCRETE_LC, '/api/class/eqptLC.xml'),
                    RestQuery(QueryId.CONCRETE_FCSlot, '/api/class/eqptFCSlot.xml'),
                    RestQuery(QueryId.CONCRETE_FC, '/api/class/eqptFC.xml'),
                ])

            # LLDP, CDP and ELTMC from leafs
            if node_role == LEAF:
                queries.extend(
                    cls.SwitchQueries.getLldpQueries(node_intf_list))
                queries.extend(cls.SwitchQueries.getCdpQueries())
                queries.extend(cls.SwitchQueries.getEltmQueries())

            return queries

        @staticmethod
        def getFibQueries(node_role, node_fcs):
            fib_cmd_lc = "vsh_lc -c 'show forwarding ipv4 route vrf all'"
            fib_cmd_lc_v6 = "vsh_lc -c 'show forwarding ipv6 route vrf all'"
            queries = []
            if node_role == LEAF:
                queries.append(SshQuery(QueryId.HARDWARE_FIB, fib_cmd_lc))
                queries.append(SshQuery(QueryId.HARDWARE_FIB_V6, fib_cmd_lc_v6))
            elif node_role == SPINE:
                if node_fcs is not None and len(node_fcs) > 0:
                    for each_fc in node_fcs:
                        ssh_pass_cmd = 'sshpass -p root ssh -o StrictHostKeyChecking=no '
                        fc_cmd = "root@fc%s " % each_fc
                        vsh_cmd = "/lc/isan/bin/vsh_lc -c " + """'show forwarding ipv4 route vrf all'"""
                        fib_cmd = '"%s"' % vsh_cmd
                        fib_cmd_fabric_card = ssh_pass_cmd + fc_cmd + fib_cmd
                        vsh_cmd_v6 = "/lc/isan/bin/vsh_lc -c " + """'show forwarding ipv6 route vrf all'"""
                        fib_cmd_v6 = '"%s"' % vsh_cmd_v6
                        fib_cmd_fabric_card_v6 = ssh_pass_cmd + fc_cmd + fib_cmd_v6
                        query = SshQuery(QueryId.HARDWARE_FIB_SPINEFC, fib_cmd_fabric_card)
                        query.setQueryParamSpineFc(each_fc)
                        queries.append(query)
                        query = SshQuery(QueryId.HARDWARE_FIB_SPINEFC_V6, fib_cmd_fabric_card_v6)
                        query.setQueryParamSpineFc(each_fc)
                        queries.append(query)
                else:
                    queries.append(SshQuery(QueryId.HARDWARE_FIB, fib_cmd_lc))
                    queries.append(SshQuery(QueryId.HARDWARE_FIB_V6, fib_cmd_lc_v6))
            return queries

        @staticmethod
        def getLldpQueries(node_intf_list):
            queries = [
                SshQuery(
                    QueryId.HARDWARE_LLDP_ENTRY,
                    "vsh -c 'show lldp entry'")]
            # TODO: need to get 'show lldp interface ethernet for all
            # interfaces'
            return queries

        @staticmethod
        def getCdpQueries():
            queries = [
                SshQuery(
                    QueryId.HARDWARE_CDP_ENTRY,
                    "vsh -c 'show cdp all'"),
                SshQuery(
                    QueryId.HARDWARE_CDP_NEIGHBOR,
                    "vsh -c 'show cdp neighbors detail'")]
            return queries

        @staticmethod
        def getEltmQueries():
            queries = [
                # SshQuery(QueryId.HARDWARE_ELTMC, "vsh_lc -c 'show system internal eltmc info vlan all'"),
                SshQuery(QueryId.HARDWARE_ELTMC_INTF, "vsh_lc -c 'show system internal eltmc info interface all'"),
                SshQuery(QueryId.HARDWARE_ELTMC_VLAN_SUMMARY,
                         "vsh_lc -c 'show system internal eltmc info vlan summary'"),
                # SshQuery(QueryId.HARDWARE_ELTMC_VLAN_BRIEF, "vsh_lc -c 'show system internal eltmc info vlan brief'"),
            ]
            return queries

        @staticmethod
        def getASICCmds(cls, asic_type):
            if asic_type == AsicType.DONNER:
                return cls.SwitchQueries.getDonnerCmds()
            elif asic_type == AsicType.MILLER:
                return cls.SwitchQueries.getNorthStarCmds()
            elif asic_type == AsicType.SUGARBOWL:
                return cls.SwitchQueries.getSugarBowlCmds()
            elif asic_type == AsicType.HOMEWOOD:
                return cls.SwitchQueries.getHomewoodCmds()
            elif asic_type == AsicType.HEAVENLY:
                # Keeping same as Homewood as Heavenly has similar commands
                return cls.SwitchQueries.getHomewoodCmds()
            elif asic_type == AsicType.WOLFRIDGE:
                # Keeping same as Homewood as Heavenly has similar commands
                return cls.SwitchQueries.getHomewoodCmds()
            else:
                cls.logger.debug("AsicType not initalized")
            return []

        @staticmethod
        def getNorthStarCmds():
            northstar_cmds = [
                "vsh_lc -c 'show platform internal ns table mth_lux_slvy_DHS_AClassKeyTable_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slvy_DHS_AClassDataTable_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slvz_DHS_SecurityGroupKeyTable0_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slvz_DHS_SecurityGroupKeyTable1_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slvy_DHS_SecurityGroupKeyTable2_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slvy_DHS_SecurityGroupKeyTable3_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slvz_DHS_SecurityGroupDataTable0_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slvz_DHS_SecurityGroupDataTable1_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slvy_DHS_SecurityGroupDataTable2_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slvy_DHS_SecurityGroupDataTable3_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slve_DHS_QosMapTable_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_rwx_slva_DHS_RwAdjTable_memif_data egress all'",
                "vsh_lc -c 'show system internal aclqos range-resource'",
                "vsh_lc -c 'show system internal aclqos zoning-rules'"]
            return northstar_cmds

        @staticmethod
        def getDonnerCmds():
            donner_cmds = [
                "vsh_lc -c 'show platform internal ns table mth_luxh_slvp_DHS_AClassKeyTable_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_luxh_slvp_DHS_AClassDataTable_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_luxh_slvq_DHS_SecurityGroupKeyTable0_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_luxh_slvr_DHS_SecurityGroupKeyTable1_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_luxh_slvs_DHS_SecurityGroupKeyTable2_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_luxh_slvt_DHS_SecurityGroupKeyTable3_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_luxh_slvu_DHS_SecurityGroupDataTable0_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_luxh_slvu_DHS_SecurityGroupDataTable1_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_luxh_slvv_DHS_SecurityGroupDataTable2_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_luxh_slvv_DHS_SecurityGroupDataTable3_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_lux_slve_DHS_QosMapTable_memif_data egress all'",
                "vsh_lc -c 'show platform internal ns table mth_rwx_slva_DHS_RwAdjTable_memif_data egress all'",
                "vsh_lc -c 'show system internal aclqos range-resource'",
                "vsh_lc -c 'show system internal aclqos zoning-rules'", ]
            return donner_cmds

        @staticmethod
        def getSugarBowlCmds():
            sugarbowl_cmds = [
                "vsh_lc -c 'show platform internal hal objects policy zoningrule'",
                "vsh_lc -c 'show system internal aclqos zoning-rules'",
                #                 "vsh_lc -c 'show system internal aclqos services redir'",
                "vsh_lc -c 'show platform internal sug table tah_sug_lud_qosmaptable all'",
                "vsh_lc -c 'show platform internal hal health-stats'",
            ]

            return sugarbowl_cmds

        @staticmethod
        def getHomewoodCmds():
            sugarbowl_cmds = [
                "vsh_lc -c 'show platform internal hal objects policy zoningrule'",
                "vsh_lc -c 'show system internal aclqos zoning-rules'",
                #                 "vsh_lc -c 'show system internal aclqos services redir'",
                "vsh_lc -c 'show platform internal sug table tah_sug_lud_qosmaptable all'",
                "vsh_lc -c 'show platform internal hal health-stats'",
                "vsh_lc -c 'show platform internal hal objects policy capability'"
            ]

            return sugarbowl_cmds

    class MsoQueries:

        @staticmethod
        def getQueries():
           queries = [
               RestQuery(QueryId.MSO_SITES, '/api/v1/sites'),
               RestQuery(QueryId.MSO_FABRIC_CONNECTIVITY, '/api/v1/sites/fabric-connectivity'),
               RestQuery(QueryId.MSO_FABRIC_CONNECTIVITY_STATUS, '/api/v1/sites/fabric-connectivity-status'),
               RestQuery(QueryId.MSO_SCHEMAS, '/api/v1/schemas'),
               RestQuery(QueryId.MSO_TENANTS, '/api/v1/tenants')
           ]
           return queries

        @staticmethod
        def getQueryIds():
            msoQueryIds = [x.getQueryId() for x in GenericCollector.MsoQueries.getQueries()]
            # Below are dynamically created queries not present in getQueries.
            msoQueryIds.append(QueryId.MSO_POLICY_REPORT)
            return msoQueryIds

        @staticmethod
        def getMsoTenantList(cls, node):
            cls.logger.info(
                "Collecting MSO tenants information from node:%s ip:%s role:%s" %
                (node.node_name, node.getNodeIp(), node.node_role))
            mso_tenant_uri = "/api/v1/tenants"
            tenant_list = []
            rest_access = None

            try:
                mso_url = cls.create_base_url(cls.protocol, node.getNodeIp(), cls.port)

                login_time_out , query_time_out, node_time_out  = cls.getNodeTimeOut(node)
                session = MSOLoginSession(mso_url, cls.user, cls.password, timeout=node_time_out,
                                          request_format='json')
                rest_access = DirectRestAccess(session)
                rest_access.login()

                rsp_status_code, rsp_text = rest_access.getRawResponse(mso_url + mso_tenant_uri)
                if rsp_status_code == requests.codes.ok:
                    for tenant in json.loads(rsp_text)['tenants']:
                        tenant_list.append(tenant['name'])
                else:
                    cls.logger.error("REST Error: %s" % rsp_status_code)
            except Exception as e:
                cls.logger.warning("MSO Tenant list lookup failed, Reason: %s" % str(e))
            finally:
                if rest_access is not None:
                    try:
                        rest_access.logout()
                    except Exception as e:
                        cls.logger.warning("logout failed due to: %s"%str(e))

            return tenant_list

        @staticmethod
        def getMsoPolicyReportQuery(cls, node):
            mso_policy_report_queries = []
            tenants = cls.MsoQueries.getMsoTenantList(cls, node)
            # Split policy-report queries into batches. There is no getAll option for policy-report,
            # and sending individually took more time than batching the requests.
            for i in range(0, len(tenants), MSO_TENANTS_PER_POLICY_REPORT):
                mso_policy_report_uri = '/api/v1/policy-report?tenants=' + \
                                        ",".join(tenants[i:i+MSO_TENANTS_PER_POLICY_REPORT])
                mso_policy_report_queries.append(RestQuery(QueryId.MSO_POLICY_REPORT, mso_policy_report_uri))

            return mso_policy_report_queries

    class StandaloneQueries:

        @staticmethod
        def getQueries(node_role=None, sa_fabric=None, node_version=None):
            queries = []
            if node_role in [STANDALONE_LEAF]:
                queries = [
                    RestQuery(QueryId.NX_FABRIC_GET_SUPPORTED_FEATURE, '/api/mo/sys/fm.json?rsp-subtree=full',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_EPS, '/api/mo/sys/eps.json?rsp-subtree=full',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_L3INST, '/api/mo/sys.json?rsp-subtree=full&rsp-subtree-class=l3Ctx,l3Inst,l2BD,vlanCktEp,'
                                                        'l2RsPathDomAtt&query-target=subtree&target-subtree-class=l3Ctx,l3Inst',
                              standalone=True),
                    RestQuery(QueryId.NX_FABRIC_L3INST_V2, '/api/mo/sys.json?rsp-subtree=full&rsp-subtree-class=l3Inst',
                              standalone=True),
                    SshQuery(QueryId.NX_FABRIC_SHOW_VXLAN, "show vxlan",
                             standalone=True, features = "fmNvo fmEvpn"),
                    SshQuery(QueryId.NX_FABRIC_VPC_BRIEF, "show vpc brief | json",
                              standalone = True, features = "fmVpc"),
                    SshQuery(QueryId.NX_FABRIC_VPC_CONSISTENCY_VLANS, "show vpc consistency-parameters vlan | json",
                              standalone = True, features = "fmVpc"),
                    SshQuery(QueryId.NX_FABRIC_VPC_CONSISTENCY_GLOBAL, "show vpc consistency-parameters global | json",
                              standalone = True, features = "fmVpc"),
                    SshQuery(QueryId.NX_FABRIC_VPC_CONSISTENCY_VNI, "show vpc consistency-parameters vni | json",
                              standalone = True, features = "fmVpc"),
                    RestQuery(QueryId.NX_FABRIC_VPC, '/api/mo/sys/vpc.json?rsp-subtree=full',
                              standalone = True, features = "fmVpc"),
                    RestQuery(QueryId.NX_FABRIC_NVE_INFRAVLAN, '/api/mo/sys/pltfm/nve-1.json?rsp-subtree=full',
                              standalone = True),
                    SshQuery(QueryId.NX_FABRIC_PC_SUMMARY, "show port-channel summary | json",
                             standalone=True),
                    RestQuery(QueryId.NX_FABRIC_LACP, '/api/mo/sys/lacp.json?rsp-subtree=full&rsp-subtree-class=lacpIf',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_PHY_INTERFACE, '/api/mo/sys/intf.json?query-target=subtree&target-subtree-class=l1PhysIf,ethpmPhysIf',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_PC_INTERFACE, '/api/mo/sys/intf.json?query-target=subtree&rsp-subtree=children&rsp-subtree-class=pcBndlMbrIf&target-subtree-class=pcAggrIf,ethpmAggrIf',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_STP, '/api/mo/sys/stp.json?query-target=subtree&target-subtree-class=stpIf',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_SVI_INTERFACE, '/api/mo/sys/intf.json?rsp-subtree=full&rsp-subtree-class=sviIf',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_ICMPV4, '/api/mo/sys/icmpv4.json?query-target=subtree&target-subtree-class=icmpv4If',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_ICMPV6, '/api/mo/sys/icmpv6.json?query-target=subtree&target-subtree-class=icmpv6If',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_IPV4, '/api/mo/sys/ipv4.json?rsp-subtree=full&rsp-subtree-class=ipv4Dom,ipv4If,ipv4Addr',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_IPV6, '/api/mo/sys/ipv6.json?rsp-subtree=full&rsp-subtree-class=ipv6Dom,ipv6If,ipv6Addr',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_HMM, '/api/mo/sys/hmm.json?rsp-subtree=full',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_PIM, '/api/mo/sys/pim.json?query-target=subtree&rsp-subtree=children&rsp-subtree-class=pimAdjEp&target-subtree-class=pimIf',
                              standalone = True, features = "fmPim"),
                    RestQuery(QueryId.NX_FABRIC_OSPF, '/api/mo/sys/ospf.json?rsp-subtree=full&rsp-subtree-class=ospfAdjEp,ospfIf,ospfDom,ospfRoute',
                              standalone = True, features = "fmOspf"),
                    RestQuery(QueryId.NX_FABRIC_BGP, '/api/mo/sys/bgp.json?rsp-subtree=full',standalone=True, features = "fmBgp"),
                    RestQuery(QueryId.NX_FABRIC_EVPN, '/api/mo/sys/evpn.json?rsp-subtree=full',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_LOOPBACK_INTF,
                              '/api/mo/sys/intf.json?query-target=subtree&target-subtree-class=l3LbRtdIf,ethpmLbRtdIf',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_ISIS_INFO,
                              '/api/mo/sys/isis.json?query-target=subtree&rsp-subtree=children&target-subtree-class=isisIf',
                              standalone=True, features = "fmIsis"),
                    SshQuery(QueryId.NX_FABRIC_ISIS_ADJACENCY, "show isis adjacency | json",
                              standalone=True, features = "fmIsis"),
                    SshQuery(QueryId.NX_FABRIC_PIM_NEIGHBOR, "show ip pim neighbor | json",
                              standalone=True, features = "fmPim"),

                    SshQuery(QueryId.NX_FABRIC_SHOW_VERSION, "show version",
                             standalone=True),
                    SshQuery(QueryId.NX_FABRIC_MAC_TABLE, "show mac address-table",
                              standalone=True),
                    SshQuery(QueryId.NX_FABRIC_SHOW_IP_ARP_VRF, "show ip arp vrf all", standalone=True),
                    SshQuery(QueryId.NX_FABRIC_SHOW_IPV4_ROUTE, "show ip route vrf all", standalone=True),
                    SshQuery(QueryId.NX_FABRIC_SHOW_IPV6_ROUTE, "show ipv6 route vrf all", standalone=True),

                    SshQuery(QueryId.NX_FABRIC_SHOW_RUN_CONFIG, "show running-config expand-port-profile", standalone=True),
                    SshQuery(QueryId.NX_FABRIC_PIM_INTERFACE, "show ip pim interface | json",
                             standalone=True, features = "fmPim"),
                    SshQuery(QueryId.NX_FABRIC_OSPF_NEIGHBORS, "show ip ospf neighbors | json",
                             standalone=True, features = "fmOspf"),
                    RestQuery(QueryId.NX_FABRIC_VRF_LIST, '/api/node/class/l3Inst.json',
                              standalone=True),
                    RestQuery(QueryId.NX_FABRIC_BD, '/api/mo/sys/bd.json?rsp-subtree=full',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_HSRP, '/api/mo/sys/hsrp.json?query-target=subtree&target-subtree-class=hsrpIf',
                              standalone = True),
                    RestQuery(QueryId.CONCRETE_LC, '/api/class/eqptLC.xml',
                              standalone = True),
                    RestQuery(QueryId.CONCRETE_L1PHYSIF, '/api/node/class/l1PhysIf.xml',
                              standalone = True)
                ]
            elif node_role == STANDALONE_SPINE :
                queries = [
                    RestQuery(QueryId.NX_FABRIC_GET_SUPPORTED_FEATURE, '/api/mo/sys/fm.json?rsp-subtree=full',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_L3INST_V2, '/api/mo/sys.json?rsp-subtree=full&rsp-subtree-class=l3Inst',
                              standalone=True),
                    RestQuery(QueryId.NX_FABRIC_L3INST, '/api/mo/sys.json?rsp-subtree=full&rsp-subtree-class=l3Ctx,l3Inst,l2BD,vlanCktEp,'
                                                        'l2RsPathDomAtt&query-target=subtree&target-subtree-class=l3Ctx,l3Inst',
                              standalone=True),
                    RestQuery(QueryId.NX_FABRIC_OSPF, '/api/mo/sys/ospf.json?rsp-subtree=full&rsp-subtree-class=ospfAdjEp,ospfIf,ospfDom,ospfRoute',
                              standalone = True, features = "fmOspf"),
                    RestQuery(QueryId.NX_FABRIC_BGP, '/api/mo/sys/bgp.json?rsp-subtree=full',standalone=True, features = "fmBgp"),
                    RestQuery(QueryId.NX_FABRIC_PHY_INTERFACE, '/api/mo/sys/intf.json?query-target=subtree&target-subtree-class=l1PhysIf,ethpmPhysIf',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_PC_INTERFACE, '/api/mo/sys/intf.json?query-target=subtree&rsp-subtree=children&rsp-subtree-class=pcBndlMbrIf&target-subtree-class=pcAggrIf,ethpmAggrIf',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_VPC, '/api/mo/sys/vpc.json?rsp-subtree=full',
                              standalone = True, features = "fmVpc"),
                    RestQuery(QueryId.NX_FABRIC_STP, '/api/mo/sys/stp.json?query-target=subtree&target-subtree-class=stpIf',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_ISIS_INFO, '/api/mo/sys/isis.json?query-target=subtree&rsp-subtree=children&target-subtree-class=isisIf', standalone=True, features = "fmIsis"),
                    SshQuery(QueryId.NX_FABRIC_ISIS_ADJACENCY, "show isis adjacency | json",
                             standalone=True, features = "fmIsis"),
                    RestQuery(QueryId.NX_FABRIC_LOOPBACK_INTF, '/api/mo/sys/intf.json?query-target=subtree&target-subtree-class=l3LbRtdIf,ethpmLbRtdIf',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_IPV4, '/api/mo/sys/ipv4.json?rsp-subtree=full&rsp-subtree-class=ipv4Dom,ipv4If,ipv4Addr',
                              standalone = True),
                    RestQuery(QueryId.NX_FABRIC_IPV6, '/api/mo/sys/ipv6.json?rsp-subtree=full&rsp-subtree-class=ipv6Dom,ipv6If,ipv6Addr',
                              standalone = True),

                    SshQuery(QueryId.NX_FABRIC_SHOW_IPV4_ROUTE, "show ip route vrf all", standalone=True),
                    SshQuery(QueryId.NX_FABRIC_SHOW_IPV6_ROUTE, "show ipv6 route vrf all", standalone=True),
                    SshQuery(QueryId.NX_FABRIC_SHOW_VERSION, "show version",
                             standalone=True),
                    RestQuery(QueryId.CONCRETE_LC, '/api/class/eqptLC.xml',
                              standalone=True),
                    RestQuery(QueryId.CONCRETE_FC, '/api/class/eqptFC.xml',
                              standalone = True),
                    RestQuery(QueryId.CONCRETE_FCSlot, '/api/class/eqptFCSlot.xml',
                              standalone = True),
                ]
            elif node_role == DCNM :
                prefix_api = DcnmVersionApiUtils.getPrefixApi(node_version)
                queries = []
                # version api is deprecated after 12.0
                if not prefix_api:
                    queries.append(RestQuery(QueryId.NX_FABRIC_DCNM_VERSION, prefix_api + '/rest/dcnm-version',
                                             standalone = True))
                queries.append(RestQuery(QueryId.NX_FABRIC_DCNM_LINKS, prefix_api + '/rest/control/links/fabrics/{0}'.format(sa_fabric),
                                         standalone = True))
            return queries

        @staticmethod
        def getInventoryQuery(sa_fabric, node_version):
            prefix_api = DcnmVersionApiUtils.getPrefixApi(node_version)
            return RestQuery(QueryId.NX_FABRIC_DCNM_INVENTORY, prefix_api + '/rest/control/fabrics/{0}/inventory'.format(sa_fabric),
                          standalone = True)

        @staticmethod
        def getStandaloneInbQuery(node, fabric_id):
            prefix_api = DcnmVersionApiUtils.getPrefixApi(node.getVersion())
            query_cmd_base = ""
            if prefix_api:
                query_cmd_base = prefix_api + "/lan-fabric/rest/globalInterface/?navId=%d&filter=ifName==Loopback%d"
            else:
                query_cmd_base = "/rest/globalInterface/?navId=%d&ifName=*Loopback%d*"
            query_cmd = query_cmd_base%(fabric_id, node.getLoopbackInterface())
            return RestQuery(QueryId.NX_FABRIC_DCNM_GLOBAL_INTERFACE,
                             query_cmd, standalone=True)

        @staticmethod
        def useDirectRest(cls, node, query):
            if node.isLoginSuccess():
                cls.logger.info("Retrieving %s from node:%s ip:%s port:%s role:%s"
                                % (query.getQueryString(), node.node_name, node.getNodeIp(), node.getNodePort(), node.node_role))
                rest_access = None
                try:
                    switch_url = cls.create_base_url(cls.protocol, node.getNodeIp(), node.getNodePort())
                    login_time_out , query_time_out, node_time_out  = cls.getNodeTimeOut(node)
                    user_name = cls.user
                    password = cls.password
                    if cls.lan_username is not None and cls.lan_password is not None:
                        user_name = cls.lan_username
                        password = cls.lan_password
                        cls.logger.debug("Using lan credentials provided for node:%s ip:%s role:%s"
                                         % (node.node_name, node.getNodeIp(), node.node_role))
                    if cls.leaf_list is not None and cls.leaf_list.get(node.getNodeIp()) is not None:
                        user_name = cls.leaf_list.get(node.getNodeIp()).get("userName")
                        password = cls.leaf_list.get(node.getNodeIp()).get("passWord")
                        cls.logger.debug("Using leaf credentials provided for node:%s ip:%s role:%s"
                                         % (node.node_name, node.getNodeIp(), node.node_role))
                    session = LoginSession(switch_url,
                                           user_name,
                                           password,
                                           timeout=(login_time_out, query_time_out),
                                           request_format='json')
                    rest_access = DirectRestAccess(session)
                    rest_access.login()
                    cls.queryRest(rest_access, node, query)
                except Exception as e:
                    cls.logger.error("Failed to retrieve %s from node:%s ip:%s role:%s, Reason: %s"
                                     % (query.getQueryString(), node.node_name, node.getNodeIp(), node.node_role, str(e)))
                finally:
                    if rest_access is not None:
                        try:
                            rest_access.logout()
                        except Exception as e:
                            cls.logger.warning("Rest logout failed while retrieving %s, Reason: %s" % (query.getQueryString(), str(e)))

        @staticmethod
        def keyLookup(element, keyChain, default=None):
            if element is not None:
                current_level = element
            else:
                return default
            for key in keyChain:
                if key in current_level:
                    current_level = current_level[key]
                elif not isinstance(key, str) and isinstance(current_level, list):
                    if key < len(current_level):
                        current_level = current_level[key]
                else:
                    return default
            return current_level

        @staticmethod
        def getVpcInterfaceList(cls, node):
            vpc_interface_list = []
            try:
                vpc_query_response = None
                vpc_query = '/api/mo/sys/vpc.json?rsp-subtree=full'
                query = RestQuery(QueryId.NX_FABRIC_VPC, vpc_query, standalone = True, features = "fmVpc")
                query.setQueryString("vpc_interface_list")
                cls.StandaloneQueries.useDirectRest(cls, node, query)
                if query.query_response is not None:
                    vpc_query_response = GlobalUtils.gzipDecompress(cls, query.query_response)
                if vpc_query_response is not None:
                    vpc_instance_chain = ['imdata', 0, 'vpcEntity', 'children', 0, 'vpcInst', 'children']
                    vpc_instance_children = cls.StandaloneQueries.keyLookup(json.loads(vpc_query_response), vpc_instance_chain)
                    vpc_domain_chain = ['vpcDom', 'children']
                    vpc_domain_children = cls.StandaloneQueries.keyLookup(
                        next((node for node in (vpc_instance_children or []) if 'vpcDom' in node), None), vpc_domain_chain)

                    for entry in (vpc_domain_children or []):
                        if 'vpcKeepalive' in entry:
                            peer_link_chain = ['vpcKeepalive', 'children', 0, 'vpcPeerLink', 'attributes', 'id']
                            peer_link_id = cls.StandaloneQueries.keyLookup(entry, peer_link_chain)
                            if peer_link_id is not None:
                                vpc_interface_list.append(peer_link_id.split("po")[1])
                        elif 'vpcIf'in entry:
                            vpc_leg_chain = ['vpcIf', 'children', 0, 'vpcRsVpcConf', 'attributes', 'tSKey']
                            vpc_leg_id = cls.StandaloneQueries.keyLookup(entry, vpc_leg_chain)
                            if vpc_leg_id is not None:
                                vpc_interface_list.append(vpc_leg_id.split("po")[1])

            except Exception as e:
                cls.logger.error("Failed to parse vpc_interface_query from node:%s ip:%s role:%s, Reason: %s"
                                 % (node.node_name, node.getNodeIp(), node.node_role, str(e)))
            return vpc_interface_list

        @staticmethod
        def getVpcInterfaceConsistencyQueries(cls, node):
            vpc_interface_consistency_queries = []
            if node.isLoginSuccess():
                # vpc_interface_list = vpc_legs + peer_link
                vpc_interface_list = cls.StandaloneQueries.getVpcInterfaceList(cls, node)
                for port_channel in vpc_interface_list:
                    vpc_interface_consistency_query = 'show vpc consistency-parameters interface port-channel ' + port_channel + ' | json'
                    vpc_interface_consistency_queries.append(SshQuery(QueryId.NX_FABRIC_VPC_CONSISTENCY_INTERFACE,
                                                                      vpc_interface_consistency_query,
                                                                      standalone=True))
            return vpc_interface_consistency_queries

        @staticmethod
        def getVrfList(cls, node):
            vrf_list = []
            if node.isLoginSuccess():
                cls.logger.info("Retrieving vrf-list from node:%s ip:%s port:%s role:%s"
                                % (node.node_name, node.getNodeIp(), node.getNodePort(), node.node_role))
                rest_access = None
                try:
                    switch_url = cls.create_base_url(cls.protocol, node.getNodeIp(), node.getNodePort())
                    login_time_out , query_time_out, node_time_out  = cls.getNodeTimeOut(node)
                    user_name = cls.user
                    password = cls.password
                    if cls.lan_username is not None and cls.lan_password is not None:
                        user_name = cls.lan_username
                        password = cls.lan_password
                        cls.logger.debug("Using lan credentials provided for node:%s ip:%s role:%s"
                                         % (node.node_name, node.getNodeIp(), node.node_role))
                    if cls.leaf_list is not None and cls.leaf_list.get(node.getNodeIp()) is not None:
                        user_name = cls.leaf_list.get(node.getNodeIp()).get("userName")
                        password = cls.leaf_list.get(node.getNodeIp()).get("passWord")
                        cls.logger.debug("Using leaf credentials provided for node:%s ip:%s role:%s"
                                        % (node.node_name, node.getNodeIp(), node.node_role))
                    session = LoginSession(switch_url,
                                           user_name,
                                           password,
                                           timeout=(login_time_out, query_time_out),
                                           request_format='json')
                    rest_access = DirectRestAccess(session)
                    rest_access.login()
                    status, vrf_query_response = rest_access.getRawResponse(switch_url + '/api/node/class/l3Inst.json')
                    for each_entry in json.loads(vrf_query_response)['imdata']:
                        vrf_list.append(each_entry['l3Inst']['attributes']['dn'].split("-", 1)[1])
                except Exception as e:
                    cls.logger.error("Failed to retrieve vrf-list from node:%s ip:%s role:%s, Reason: %s"
                                     % (node.node_name, node.getNodeIp(), node.node_role, str(e)))
                finally:
                    if rest_access is not None:
                        try:
                            rest_access.logout()
                        except Exception as e:
                            cls.logger.warning("Rest logout failed while retrieving vrf-list, Reason: %s" % str(e))
            return vrf_list

        @staticmethod
        def getPerVrfQueries(cls, node):
            per_vrf_queries = []
            vrf_list = cls.StandaloneQueries.getVrfList(cls, node)
            for vrf_name in vrf_list:
                vrf_query = 'show ip arp vrf ' + vrf_name
                per_vrf_queries.append(SshQuery(QueryId.NX_FABRIC_SHOW_IP_ARP_VRF,
                                                vrf_query,
                                                standalone=True)
                                       .setQueryParamVrfName(vrf_name)
                                       .setQueryParamVrfCount(len(vrf_list)))
            return per_vrf_queries

        @staticmethod
        def runInventoryQuery(cls, node):
            query = cls.StandaloneQueries.getInventoryQuery(node.getSaFabric(), node.getVersion())
            cls.createQuery(node, query)
            node_collection_stats = NodeCollectionStats(cls.logger, node, 1,
                                                        round(time.time()))
            rest_access = None
            try:
                rest_access = cls.initializeConnection(node, cls.user, cls.password,
                                                       cls.protocol, cls.port,
                                                       node_collection_stats)[0]
                if rest_access:
                    cls.queryRest(rest_access, node, query)
            except Exception as e:
                cls.logger.error("Error trying to run inventory query: %s"%str(e))
            finally:
                if rest_access:
                    try:
                        rest_access.logout()
                    except Exception as e:
                        cls.logger.warning("Unable to logout of DCNM session while querying inventory: %s"%str(e))

            # avoid re-collecting this query
            cls.emitOrSaveQueryResult(query)
            # node_collection_stats.setFailedQuery(query)
            # cls.getAndUpdateCollectionTime(node_collection_stats,
            #                                cls.getNodeTimeOut(node)[2])
            # cls.updateNodeStats(node, node_collection_stats)
            return query

        @staticmethod
        def createStandaloneInbQuery(cls, node):
            try:
                query = cls.StandaloneQueries.runInventoryQuery(cls, node)
                if not query.isSuccess():
                    raise Exception("Collecting inventory query failed!")

                fabric_id = None
                node_info_list = json.loads(GlobalUtils.gzipDecompress(cls, query.getQueryResponse()[0]))
                for node_info in node_info_list:
                    fabric_id = node_info.get("fid")
                    if fabric_id and node_info["fabricName"].lower() != node.getSaFabric().lower():
                        break;
                cls.logger.debug("Retrieved fabric id: %d"%fabric_id)

                if fabric_id or fabric_id == 0:
                    return cls.StandaloneQueries.getStandaloneInbQuery(node, fabric_id)
            except Exception as e:
                cls.logger.warning("Unable to create inband query due to: %s"%str(e))
            return None

    class VCenterQueries:

        @staticmethod
        def getQueries():
            queries = [VCenterQuery(QueryId.VCENTER_VCENTER, '/vcenter/all')]
            return queries

    class F5Queries:

        @staticmethod
        def getQueries():
            if F5_ACCESS == 'rest':
                queries = [
                    RestQuery(QueryId.F5_SYSTEM, '/mgmt/tm/cm/device'),
                    RestQuery(QueryId.F5_NETWORK, '/mgmt/tm/net/interface'),
                    RestQuery(QueryId.F5_ARP, '/mgmt/tm/net/arp/stats'),
                    RestQuery(QueryId.F5_POOL, '/mgmt/tm/ltm/pool?expandSubcollections=true'),
                    RestQuery(QueryId.F5_VLAN, '/mgmt/tm/net/vlan?expandSubcollections=true'),
                    RestQuery(QueryId.F5_SELF_IP, '/mgmt/tm/net/self'),
                    RestQuery(QueryId.F5_VIRTUAL, '/mgmt/tm/ltm/virtual-address?expandSubcollections=true')]

            else:
                queries = [
                    F5Query(QueryId.F5_SYSTEM, '/mgmt/tm/cm/device'),
                    F5Query(QueryId.F5_NETWORK, '/mgmt/tm/net/interface'),
                    F5Query(QueryId.F5_ARP, '/mgmt/tm/net/arp/stats'),
                    F5Query(QueryId.F5_POOL, '/mgmt/tm/ltm/pool?expandSubcollections=true'),
                    F5Query(QueryId.F5_VLAN, '/mgmt/tm/net/vlan?expandSubcollections=true')]

            queryIds = [x.getQueryId() for x in queries]
            return queries, queryIds

    class NetScalerQueries:

        @staticmethod
        def getQueries():
            queries = [
                NetScalerQuery(
                    QueryId.NETSCALER_SYSTEM,
                    '/ns/system'),
                NetScalerQuery(
                    QueryId.NETSCALER_NETWORK,
                    '/ns/system/network'),
                NetScalerQuery(
                    QueryId.NETSCALER_LB,
                    '/ns/traffic_mgmt/lb'),
                NetScalerQuery(
                    QueryId.NETSCALER_GSLB,
                    '/ns/traffic_mgmt/gslb')]
            queryIds = [x.getQueryId() for x in queries]
            return queries, queryIds

    class CollectionAbortedException(Exception):
        pass

    class ExecutionAbortedException(Exception):
        pass

    def __init__(
            self,
            logger,
            user,
            password,
            partition_index,
            partition_count,
            login_time_out=6,
            query_time_out=60,
            node_time_out=120,
            apic_login_time_out=6,
            apic_query_time_out=60,
            apic_node_time_out=120,
            protocol='https',
            port='443',
            max_threads=16,
            iteration=None,
            call_back=None,
            cnae_mode=_APIC,
            lan_username=None,
            lan_password=None,
            leaf_list=None,
            populate_login_failures=False):
        self.user = user
        self.password = password
        self.protocol = protocol
        self.port = port
        self.max_threads = max_threads
        self.partition_index = partition_index
        self.partition_count = partition_count
        self.login_time_out = login_time_out
        self.query_time_out = query_time_out
        self.node_time_out = node_time_out
        self.apic_login_time_out = apic_login_time_out
        self.apic_query_time_out = apic_query_time_out
        self.apic_node_time_out = apic_node_time_out
        self.logger = logger
        self.node_jobs = []
        self.topo_node_list = []
        self.iteration = iteration
        self.filter_query_ids = set()
        self.exclude_query_ids = set()
        self.pool = None
        self.output_lock = threading.Lock()
        self.call_back = call_back
        self.results = []
        self.query_info = {}
        self.optimized_query = False
        self.legacy_mode = False
        self.node_id_to_dn = {}
        self.completed_nodes = 0
        self.stats_lock = threading.Lock()
        self.collection_stats = []
        self.optimized_partition = True
        self.node_controller = []
        self.jobs = []
        self.exclude_all_queries = False
        self.cnae_mode = cnae_mode
        self.lan_username = lan_username
        self.lan_password = lan_password
        self.leaf_list = leaf_list
        self.collection_status_lock = threading.Lock()
        self.continue_collecting = True
        self.handle_pool_cleanup_internally = True
        self.job_count = 0
        self.job_count_lock = threading.Lock()
        self.populate_login_failures = populate_login_failures

    def setTopoNodeList(self, topo_node_list):
        self.topo_node_list = topo_node_list
        self.node_controller = [x for x in self.topo_node_list if x.isController()
                                or x.isMso()]

    def setFilterQueryIds(self, filter_query_ids):
        if filter_query_ids is not None:
            self.filter_query_ids = set(filter_query_ids)

    def setExcludeQueryIds(self, exclude_query_ids, exclude_all=False):
        if exclude_all == True:
            self.exclude_all_queries = True
        elif exclude_query_ids is not None:
            self.exclude_query_ids = set(exclude_query_ids)

    def setOptimizedQuery(self, optimized_query):
        self.optimized_query = optimized_query

    def setOptimizedPartition(self, optimized_partition):
        self.optimized_partition = optimized_partition

    def setLegacyMode(self, legacy_mode):
        self.legacy_mode = legacy_mode

    def setMaxThreads(self, max_threads):
        self.max_threads = max_threads

    def getLegacyMode(self):
        return self.legacy_mode

    def stop_collection(self):
        with self.collection_status_lock:
            self.continue_collecting = False

    def continue_collection(self):
        with self.collection_status_lock:
            self.continue_collecting = True

    def cleanup_pool_externally(self):
        self.handle_pool_cleanup_internally = False

    def increment_job_count(self):
        with self.job_count_lock:
            self.job_count += 1

    def is_threadpool_active(self):
        with self.job_count_lock:
            return self.job_count != len(self.jobs)

    def create_base_url(self, protocol, ip, port=443):
        if GlobalUtils.isIpv6(ip):
            ip = "[%s]"%ip
        return '%s://%s:%s' % (protocol, ip, port)

    def passesFilter(self, query_id):
        if len(self.filter_query_ids) == 0 or query_id in self.filter_query_ids:
            if query_id in self.exclude_query_ids:
                return False
            else:
                return True
        else:
            return False

    def getNodeCollectionStats(self):
        return self.collection_stats

    def getAndUpdateCollectionTime(self, node_collection_stats, node_time_out):
        if node_collection_stats:
            with self.stats_lock:
                collection_time_elapsed = (
                    round(time.time())) - node_collection_stats.getCollectionStartTime()
                collection_time_remaining = node_time_out - collection_time_elapsed
                node_collection_stats.current_collection_time = collection_time_elapsed
        return collection_time_remaining

    def process(self):
        # Partition the nodes for this GenericCollector
        node_partitioner = GenericCollectorNodePartitioner(
            self.partition_index,
            self.partition_count,
            self.optimized_partition,
            self.topo_node_list,
            self.logger)
        self.node_jobs = node_partitioner.getPartitionedNodes()
        # Collect data for this ucs collector
        if self.node_jobs:
            self.computePerNodeJobs()
            self.parallelDataCollectionAsync()

    def parallelDataCollectionAsync(self):
        self.logger.info(
            "Creating a thread pool with %d threads for collection" %
            (self.max_threads))
        # Note: default_backend() is called as it fixes requirementParse
        # error coming from cryptography module (used by paramiko).
        # This is a temporary fix, will be removed when a newer version
        # of pyca/cryptography release is available.
        default_backend()
        self.pool = ThreadPool(self.max_threads)
        '''
        Async API to return results on an output queue as received
        '''
        self.pool.imap_unordered(self.collectNodeData, self.jobs)
        if self.handle_pool_cleanup_internally:
            self.handleThreadPoolCleanup()
        # self.collectNodeSerially(self.jobs)

    def collectNodeSerially(self, jobs):
        for each_job in jobs:
            self.collectNodeData(each_job)

    def saveResults(self, query):
        self.output_lock.acquire()
        try:
            self.results.append(query)
        finally:
            self.output_lock.release()

    def getResults(self):
        return self.results

    def handleThreadPoolCleanup(self):
        if self.pool is not None:
            self.pool.close()
            self.pool.join()

    def check_if_node_is_reachable(self, node):
        try:
            node_ip = node.getNodeIp()
            ping_cmd = 'ping6' if GlobalUtils.isIpv6(node_ip) else 'ping'
            proc = subprocess.Popen([ping_cmd, '-c', '1', node_ip],
                                    stdout=subprocess.PIPE)
            stdout, stderr = proc.communicate()
        except Exception as e:
            self.logger.warning(
                "NodeId: %d, Ping test **FAILED** for ip: %s, Reason: %s" %
                (node.node_id, node.getNodeIp(), str(e)))
        else:
            if proc.returncode == 0:
                return True
            else:
                return False

    def collectNodeData(self, jobs):
        try:
            (node, queries, user, password, protocol, port, lan_username, lan_password, leaf_list) = jobs
            self.collectPerNodeData(jobs)
        except Exception as e:
            self.logger.warning(
                "NodeId: %d, Data collection FAILED Line Number: %s Reason:%s" %
                (node.node_id, sys.exc_info()[2].tb_lineno, str(e)))
        finally:
            self.increment_job_count()

    def getNodeTimeOut(self, node):
        if node.isController():
            return (
                self.apic_login_time_out,
                self.apic_query_time_out,
                self.apic_node_time_out)
        else:
            return (
                self.login_time_out,
                self.query_time_out,
                self.node_time_out)

    def initializeConnection(
            self,
            node,
            user,
            password,
            protocol,
            port,
            node_collection_stats):
        ssh = None
        rest_access = None
        vcenter_client = None
        netscaler_client = None
        f5_client = None
        url = None
        login_time_out, query_time_out, node_time_out = self.getNodeTimeOut(
            node)
        # Check for reachability
        try:
            reachable = self.check_if_node_is_reachable(node)
            node_collection_stats.setReachable(reachable)
        except Exception as e:
            self.logger.warning(
                "NodeId: %d, Reachability test failed, Reason :%s" %
                (node.node_id, str(e)))

        # Create connections
        if node.isVCenter():  # vCenter
            try:
                self.logger.info(
                    "NodeId: %d Creating vCenter client ip:%s role:%s" %
                    (node.node_id, node.node_ip, node.node_role))
                vcenter_client = VCenterClient(
                    node.node_ip, user, password, self.logger)
                node.loginSuccessful()
                node.reachable()
                node.supported()
                node_collection_stats.setVCenterLogin(True)
            except Exception as e:
                self.logger.warning(
                    ("NodeId: %d vCenter client creation FAILED, skipping collection for %s, Reason: %s" %
                     (node.node_id, node.node_ip, str(e))))
                raise CandidDataCollectionException("vcenter login failed")
        elif node.isNetScaler():  # NetScaler
            try:
                self.logger.info(
                    "NodeId: %d Creating NetScaler client ip:%s role:%s" %
                    (node.node_id, node.node_ip, node.node_role))
                netscaler_client = NetScalerClient(
                    node.node_ip, user, password, self.logger)
                node.loginSuccessful()
                node.reachable()
                node.supported()
                node_collection_stats.setNetScalerLogin(True)
            except Exception as e:
                self.logger.warning(
                    ("NodeId: %d NetScaler client creation FAILED, skipping collection for %s, Reason: %s" %
                     (node.node_id, node.node_ip, str(e))))
                raise CandidDataCollectionException("netscalar login failed")
        elif node.isF5():  # F5
            try:
                if not node.isLoginSuccess():
                    raise Exception("login failed")
                self.logger.info(
                    "NodeId: %d Creating F5 client ip:%s role:%s" %
                    (node.node_id, node.node_ip, node.node_role))
                if F5_ACCESS == 'rest':
                    session = F5Session(url, user, password,
                                        timeout=query_time_out,
                                        request_format='json')
                    rest_access = F5RestAccess(session)
                else:
                    f5_client = F5Client(node.node_ip, user, password, self.logger)

                self.logger.info(
                    "NodeId: %d Passing client creation name:%s ip:%s role:%s" %
                    (node.node_id, node.node_name, node.getNodeIp(), node.node_role))
                node.loginSuccessful()
                node.reachable()
                node.supported()
                node_collection_stats.setF5Login(True)
            except Exception as e:
                self.logger.warning(
                    ("NodeId: %d F5 client creation FAILED, skipping collection for %s, Reason: %s" %
                     (node.node_id, node.node_ip, str(e))))
                raise CandidDataCollectionException("F5 login failed")
        elif node.isDcnm():
            url = self.create_base_url(protocol, node.getNodeIp(), port)
            self.logger.info(
                "NodeId: %d Starting DCNM REST session name:%s ip:%s role:%s" %
                (node.node_id, node.node_name, node.getNodeIp(), node.node_role))
            try:
                login_session = DcnmVersionApiUtils.getLoginSession(node.getVersion())
                session = login_session(url, user, password, timeout=node_time_out,
                                           request_format='json')
                rest_access = DirectRestAccess(session)
                rest_access.login()
            except Exception as e:
                self.logger.warning(
                    "NodeId: %d DCNM REST Login Error for IP: %s , Skipping Collection  Reason:%s" %
                    (node.node_id, node.getNodeIp(), str(e)))
                self.updateNodeStats(node, node_collection_stats)
                raise CandidDataCollectionException("rest login failed")
            else:
                node_collection_stats.setRestLogin(True)
        elif node.isMso():
            url = self.create_base_url(protocol, node.getNodeIp(), port)
            self.logger.info(
                "NodeId: %d Starting MSO REST session name:%s ip:%s role:%s" %
                (node.node_id, node.node_name, node.getNodeIp(), node.node_role))
            try:
                session = MSOLoginSession(url, user, password, timeout=node_time_out,
                                           request_format='json')
                rest_access = DirectRestAccess(session)
                rest_access.login()
            except Exception as e:
                self.logger.warning(
                    "NodeId: %d MSO REST Login Error for IP: %s , Skipping Collection  Reason:%s" %
                    (node.node_id, node.getNodeIp(), str(e)))
                self.updateNodeStats(node, node_collection_stats)
                raise CandidDataCollectionException("rest login failed")
            else:
                node_collection_stats.setRestLogin(True)
        elif node.isCommandNode():
            ssh = SSHSession()
            self.logger.info(
                "NodeId: %d Starting SSH session name: %s ip:%s role:%s" %
                (node.node_id, node.node_name, node.getNodeIp(), node.node_role))
            try:
                ssh.connect(
                    node.getNodeIp(),
                    username=user,
                    password=password,
                    timeout=login_time_out)
            except Exception as e:
                self.logger.warning(
                    "NodeId: %d SSH Connection FAILED, skipping collection for %s, Reason: %s" %
                    (node.node_id, node.getNodeIp(), str(e)))
                self.updateNodeStats(node, node_collection_stats)
                raise CandidDataCollectionException("ssh login failed")
        else:
            ssh = SSHSession()
            self.logger.info(
                "NodeId: %d Starting SSH session name: %s ip:%s role:%s" %
                (node.node_id, node.node_name, node.getNodeIp(), node.node_role))
            try:
                ssh.connect(
                    node.getNodeIp(),
                    username=user,
                    password=password,
                    timeout=login_time_out)
            except Exception as e:
                self.logger.warning(
                    "NodeId: %d SSH Connection FAILED, skipping collection for %s, Reason: %s" %
                    (node.node_id, node.getNodeIp(), str(e)))
                self.updateNodeStats(node, node_collection_stats)
                raise CandidDataCollectionException("ssh login failed")
            else:
                node_collection_stats.setSshLogin(True)
                url = self.create_base_url(protocol, node.getNodeIp(), port)
                self.logger.info(
                    "NodeId: %d Starting rest session name:%s ip:%s role:%s" %
                    (node.node_id, node.node_name, node.getNodeIp(), node.node_role))
                try:
                    session = LoginSession(url, user, password, timeout=(
                        login_time_out, query_time_out), request_format='json')
                    rest_access = DirectRestAccess(session)
                    rest_access.login()
                except Exception as e:
                    self.logger.warning(
                        "NodeId: %d REST Login Error for IP: %s , Skipping Collection  Reason:%s" %
                        (node.node_id, node.getNodeIp(), str(e)))
                    self.updateNodeStats(node, node_collection_stats)
                    raise CandidDataCollectionException("rest login failed")
                else:
                    node_collection_stats.setRestLogin(True)
        return rest_access, ssh, vcenter_client, netscaler_client, f5_client

    def failQueryDueToLogin(self, query, err_msg, node_collection_stats):
        query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
        query.setQueryResponseSize(len(err_msg))
        query.setQueryResponse(err_msg, err_msg)
        self.emitOrSaveQueryResult(query)
        node_collection_stats.setFailedQuery(query)

    def collectPerNodeData(self, jobs):
        ssh = None
        rest_access = None
        vcenter_client = None
        netscaler_client = None
        f5_client = None
        (node, queries, user, password, protocol, port, lan_username, lan_password, leaf_list) = jobs
        node_collection_stats = NodeCollectionStats(
            self.logger, node, len(queries), round(time.time()))

        login_username = user
        login_password = password

        if ((node.isStandaloneSpine() or node.isStandaloneLeaf()) and (
                (lan_username is not None) and (lan_password is not None))):
            login_username = lan_username
            login_password = lan_password


        if leaf_list :
            if node.getNodeIp() in leaf_list :
                login_username = leaf_list.get(node.getNodeIp()).get("userName")
                login_password = leaf_list.get(node.getNodeIp()).get("passWord")

        rest_access, ssh, vcenter_client, netscaler_client, f5_client = (None,)*5
        try:
            (rest_access,
             ssh,
             vcenter_client,
             netscaler_client,
             f5_client) = self.initializeConnection(node,
                                                    login_username, login_password,
                                                    self.protocol, self.port,
                                                    node_collection_stats)
        except Exception as e:
            # fail all queries and re-raise exception
            if self.populate_login_failures and node.isLoginSuccess():
                err_msg = self.gzipCompress(str(e))
                for current_query in queries:
                    self.failQueryDueToLogin(current_query, err_msg, node_collection_stats)
                self.updateNodeStats(node, node_collection_stats)
            raise;

        login_time_out, query_time_out, node_time_out = self.getNodeTimeOut(
            node)

        # Fetch data
        try:
            if queries:
                jobs = [
                    (node,
                     rest_access,
                     ssh,
                     vcenter_client,
                     netscaler_client,
                     f5_client,
                     query,
                     query_time_out,
                     node_time_out,
                     node_collection_stats) for query in queries]
                # for job in jobs:
                #    self.collectNodeQueries(job)
                if self.cnae_mode in [_STANDALONE, _MSO]:
                    p = ThreadPool(min(len(queries), STANDALONE_REQUEST_PIPELINE_DEPTH))
                else:
                    p = ThreadPool(min(len(queries), REQUEST_PIPELINE_DEPTH))
                p.imap_unordered(self.collectNodeQueries, jobs)
                p.close()
                p.join()
                node_collection_stats.setCollectionTime(
                    node_collection_stats.current_collection_time)

        except Exception as e:
            self.logger.error(
                "Exception while processing queries,Line Number: %s Reason: %s" %
                (sys.exc_info()[2].tb_lineno, str(e)))

        finally:
            try:
                if rest_access:
                    rest_access.logout()
                if ssh:
                    ssh.close()
                if vcenter_client:
                    vcenter_client.close()
                if netscaler_client:
                    netscaler_client.close()
                if f5_client:
                    f5_client.close()
            except Exception as e:
                self.logger.debug(
                    "Exception while closing the sessions on node:%s Reason: %s"
                    %(node.node_id, str(e)))
        self.updateNodeStats(node, node_collection_stats)

    def collectNodeQueries(self, jobs):
        if not self.continue_collecting:
            query = jobs[6]
            error_message = COLLECTION_ABORTED_STR%("", query.getQueryCmd())
            raise GenericCollector.CollectionAbortedException(error_message)

        try:
            node,\
                rest_access, ssh, vcenter_client, netscaler_client, f5_client, \
                query,\
                query_time_out, node_time_out, node_collection_stats = jobs
            # Skip if query is legacy and mode is non-legacy
            collection_time_remaining = self.getAndUpdateCollectionTime(
                node_collection_stats, node_time_out)
            if query.isLegacyQuery():
                if not self.getLegacyMode():
                    self.logger.info("NodeId: %d, Skipping legacy query: %s" %
                                     (node.node_id, query.getQueryCmd()))
                    return
                else:
                    self.logger.info(
                        "NodeId: %d, Collecting legacy query: %s" %
                        (node.node_id, query.getQueryCmd()))

            if collection_time_remaining > query_time_out:
                if query.getQueryType() == GenericQueryResult.QueryType.REST:
                    self.queryRest(rest_access, node, query)
                elif query.getQueryType() == GenericQueryResult.QueryType.SSH:
                    self.querySsh(ssh, node, query, query_time_out)
                elif query.getQueryType() == GenericQueryResult.QueryType.VCENTER:
                    self.queryVCenter(vcenter_client, node.node_id, query)
                elif query.getQueryType() == GenericQueryResult.QueryType.NETSCALER:
                    self.queryNetScaler(netscaler_client, node.node_id, query)
                elif query.getQueryType() == GenericQueryResult.QueryType.F5_LB:
                    self.queryF5LB(f5_client, node.node_id, query)
            else:
                self.logger.warning(
                    "Node: %d, Collection time out triggered, skipping query : %s" %
                    (node.node_id, query.getQueryCmd()))
                query.setQueryResponseSize(len(NODE_TIMEOUT_STR))
                query.setQueryResponse(self.gzipCompress(NODE_TIMEOUT_STR),
                                       self.gzipCompress(NODE_TIMEOUT_STR))
                query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            self.emitOrSaveQueryResult(query)
            node_collection_stats.setFailedQuery(query)
        except Exception as e:
            self.logger.error(
                "Exception while processing query: %s, Line Number: %s Reason: %s" %
                (query.getQueryCmd(), sys.exc_info()[2].tb_lineno, str(e)))

    def updateNodeStats(self, node, node_collection_stats):
        # This is for the stats
        self.stats_lock.acquire()
        try:
            self.completed_nodes += 1
            self.collection_stats.append(node_collection_stats)
            self.logger.info(
                "Collected data for node Id: %d node Ip: %s collection time: %s" %
                (node.node_id, node.getNodeIp(), node_collection_stats.collection_time))
        except Exception as e:
            self.logger.warning(
                "NodeId: %d Collection statistics update *FAILED*,Reason: %s" %
                (node.node_id, str(e)))
        finally:
            self.stats_lock.release()

    def getCompletedNodes(self):
        return self.completed_nodes

    def queryRest(self, rest_access, node, query):
        if not FeatureManager.isQueryApplicable(self.logger, node, query):
            self.logger.error(
                "NodeId: %d, Querying: %s - Feature required for query not enabled" %
                (node.node_id, query.getQueryCmd()))
            return

        max_retries = 2
        base_url = self.create_base_url(self.protocol, node.getNodeIp(), self.port)
        url = base_url + query.getQueryCmd()
        rsp_text = None
        rsp_status_code = None
        query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
        while max_retries > 0:
            try:
                self.logger.info(
                    "NodeId: %d, Querying: %s" %
                    (node.node_id, url))
                query_start_time = int(round(time.time() * 1000))
                query.setQueryTimeMillis(query_start_time)
                if query.getQuerySubType() == GenericQueryResult.QuerySubType.GET:
                    rsp = rest_access.getRawResponseObject(url)
                    rsp_status_code = rsp.status_code
                    if rsp_status_code == requests.codes.ok:
                        query.setQueryStatus(GenericQueryResult.QueryStatus.SUCCESS)
                        #query.setQueryResponse(self.gzipCompress(rsp_text))
                        #query.setQueryResponseSize(len(rsp_text))
                        (val, count) =  self.gzipCompressRaw(rsp)
                        query.setQueryResponse(val)
                        query.setQueryResponseSize(count)
                        break
                    rsp_text = str(rsp.text)

                elif query.getQuerySubType() == GenericQueryResult.QuerySubType.POST:
                    rsp_status_code, rsp_text = rest_access.post(
                        url, query.getQueryData())

                # If response is too large, retry with paging, needed for only
                # GET
                if rsp_status_code == 400 and re.findall(
                        r'result dataset is too big', rsp_text):
                    # Retry with paging
                    self.logger.info(
                        "NodeId: %d, Requests with paging invoked for url %s" %
                        (node.node_id, url))
                    query.setQueryTimeMillis(int(round(time.time() * 1000)))
                    max_retries -= 1
                    (rsp_status_code,
                     rsp_text) = rest_access.getRawResponseWithPaging(base_url, url)
                # Handle both paging and non-paging cases together
                if rsp_status_code == requests.codes.ok:
                    query.setQueryStatus(
                        GenericQueryResult.QueryStatus.SUCCESS)
                    rsp_text = str(rsp_text)
                    query.setQueryResponse(self.gzipCompress(rsp_text))
                    query.setQueryResponseSize(len(rsp_text))
                    break
                elif rsp_status_code == 403 and re.findall(r'Token timeout', rsp_text):
                    rest_access.reauthOrLogin(self.logger)
                    self.logger.warning(
                        "NodeId: %d Cookie expired, refreshing the cookie" %
                        (node.node_id))
                    query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
                    query.setQueryResponse(
                        self.gzipCompress(COOKIE_EXPIRED_STR))
                    query.setQueryResponseSize(len(COOKIE_EXPIRED_STR))
                else:
                    self.logger.warning(
                        "NodeId: %d, Collection *FAILED* for url :%s response code = %s response text = %s" %
                        (node.node_id, url, rsp_status_code, rsp_text))
                    query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
                    query.setQueryResponseSize(len(rsp_text))
                    query.setQueryResponse(self.gzipCompress(rsp_text))
                # Common to all cases
                query_end_time = int(round(time.time() * 1000))
                query.setQueryResponseTime(query_end_time - query_start_time)
            except Exception as e:
                # Catch queries missing in offline case, json parse errors
                exception_str = str(e)
                if max_retries > 1:
                    self.logger.warning(
                        "NodeId: %d May be due to timeout while running query : %s will retry"
                        "one more time and Error details are %s" %
                        (node.node_id, url, exception_str))
                else:
                    self.logger.warning(
                        "NodeId: %d Query Failed : %s "
                        " and Error details are %s" %
                        (node.node_id, url, exception_str))
                    query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
                    query.setQueryResponseSize(len(exception_str))
                    query.setQueryResponse(self.gzipCompress(exception_str))
            finally:
                max_retries -= 1


    def querySftp(self, ssh, node, query):
        remote_path = query.getQueryParamRemotePath()
        if not remote_path:
            self.logger.warning("SFTP copy remote path not set")
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            query.setQueryResponseSize(CONFIG_EXPORT_SFTP_FILE_PATH_NOT_FOUND)
            query.setQueryResponse(self.gzipCompress(
                CONFIG_EXPORT_SFTP_FILE_PATH_NOT_FOUND))
            return

        max_retries = CONFIG_EXPORT_RETRY_COUNT
        #gzipped .tar.gz
        while max_retries > 0:
            local_file = io.BytesIO()
            try:
                ftp_client = ssh.open_sftp()
                self.logger.info("SFTP file from %s" % remote_path)
                if ftp_client.stat(remote_path).st_size:
                    ftp_client.getfo(remote_path, local_file)
                else:
                    raise Exception("Remote file %s is empty" % remote_path)
            except Exception as e:
                exception_str = str(e)
                if max_retries == 1:
                    self.logger.warning(
                        "SFTP copy error , reason:%s" %
                        exception_str)
                query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
                query.setQueryResponseSize(exception_str)
                query.setQueryResponse(self.gzipCompress(exception_str))
            else:
                query.setQueryStatus(GenericQueryResult.QueryStatus.SUCCESS)
                query_response = local_file.getvalue()
                query.setQueryResponseSize(len(query_response))
                query.setQueryResponse(query_response)
                self.logger.info(
                    "SFTP copy of config export successful")
                break
            finally:
                time.sleep(CONFIG_EXPORT_RETRY_INTERVAL)
                max_retries -= 1


    def hasError(self, bytes_stdout):
        errors = ["Error, procket", "Cmd exec error", "login failed",
                  "SSH session not active", "Incorrect command",
                  "Incomplete command", "Ambiguous command"]
        stdout_str = GlobalUtils.gzipDecompress(self, bytes_stdout).decode("utf-8")
        return any(stdout_str.find(i) != -1 for i in errors)

    def hasFailedGzipAtSwitch(self, bytes_stdout):
        """ When run bash <VSH command > | | json' | gzip
        fails at a  NXOS switch,  the switch does not return compressed status.
        It returns an error string in uncompressed form, so we have to handle
         this case before we call gzip decompress
         """
        errors = ["Cmd exec error", "Syntax error"] # NXOS switch errors
        if isinstance(bytes_stdout, bytes):
            errors = [x.encode("utf-8") for x in errors]
        if any(bytes_stdout.find(i) != -1 for i in errors):
            return True
        return False

    def checkExitStatus(self, ssh_cmd, node_id, channel, query_time_out):
        sleep_time = query_time_out/MAX_WAIT_COUNT
        wait_count = 0
        while not channel.exit_status_ready():
            if wait_count == MAX_WAIT_COUNT:
                self.logger.warn("For node: " + str(node_id) + \
                                     " cmd: " + str(ssh_cmd) + \
                                     " reached timeout: " + str(query_time_out) + \
                                     " sec for channel.exit_status_ready to be true")
                # Setting to pass, due to known paramiko issue:
                # https://github.com/paramiko/paramiko/issues/1208
                return 0
            time.sleep(sleep_time)
            wait_count += 1
        return channel.recv_exit_status()

    def querySsh(self, ssh, node, query, query_time_out):
        if not FeatureManager.isQueryApplicable(self.logger, node, query):
            self.logger.error(
                "NodeId: %d, Querying: %s - Feature required for query not enabled" %
                (node.node_id, query.getQueryCmd()))
            print("query not applicable, return" + query.getQueryCmd())
            print(str(node.enabled_features))
            print(query.getFeatureSet())
            return

        max_retries = 2
        (bytes_stdout, bytes_stderr, status) = (None, None, None)
        ssh_cmd = query.getQueryCmdWithZip() if self.cnae_mode == _APIC \
            else query.getQueryCmd()
        query_start_time = 0
        ssh_exception = None
        query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
        node_id = node.node_id
        sleep_time = SSH_TIMEOUT_SLEEP_TIME
        while max_retries > 0:
            try:
                self.logger.info(
                    "NodeId: %d, Querying: %s" %
                    (node_id, ssh_cmd))
                query_start_time = int(round(time.time() * 1000))
                query.setQueryTimeMillis(query_start_time)
                if not ssh.isActive():
                    self.logger.info(
                        "NodeId: %d, restarting unactive SSH session name:%s ip:%s role:%s" %
                        (node.node_id, node.node_name, node.getNodeIp(), node.node_role))
                    ssh.connect(node.getNodeIp(), username=self.user,
                                password=self.password,
                                timeout=self.getNodeTimeOut(node)[0])
                stdin, stdout, stderr = ssh.exec_command(
                    ssh_cmd, timeout=query_time_out)

                bytes_stdout = stdout.read() if self.cnae_mode == _APIC \
                    else self.gzipCompress(stdout.read())
                bytes_stderr = stderr.read() if self.cnae_mode == _APIC \
                    else self.gzipCompress(stderr.read())
                status = GenericQueryResult.QueryStatus.SUCCESS \
                    if (self.checkExitStatus(ssh_cmd, node_id, stdout.channel, query_time_out) == 0) else\
                    GenericQueryResult.QueryStatus.FAIL
                break
            except Exception as e:
                max_retries -=1
                ssh_exception = self.gzipCompress(str(e))
                trace = ExceptionUtils.createTraceback(traceback.format_stack())
                message = "Query (%s) failed for node id: %d, will retry " \
                            "%d more time(s) and Error details are %s"
                self.logger.warning(message%(query.getQueryCmd(), node_id,
                                          max_retries, trace))
                if ExceptionUtils.isTimeoutException(trace):
                    # In case of timeout exception, we insert a sleep
                    # before retry. Also, we double sleep time and query
                    # timeout time for next query. This is to account for
                    # a heavily loaded switch CPU to provide  it ample
                    # recovery time.
                    self.logger.info("sleeping for %d seconds"%sleep_time)
                    time.sleep(sleep_time)
                    sleep_time *= 2
                    query_time_out *= 2

        # Length comparision is done on compressed stdout.
        # stdout is compressed, stderr is NOT compressed
        is_small_response = (bytes_stdout and (len(bytes_stdout) < 300))
        if is_small_response and self.hasFailedGzipAtSwitch(bytes_stdout):
            query.setQueryResponseSize(len(bytes_stdout))
            query.setQueryResponse(bytes_stdout, bytes_stderr)
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            message = "Query (%s) failed for node id: %d with error %s"
            self.logger.warning(message%(query.getQueryCmd(), node_id,
                                         bytes_stdout))
        elif is_small_response and self.hasError(bytes_stdout):
            query.setQueryResponseSize(len(bytes_stdout))
            query.setQueryResponse(bytes_stdout, bytes_stderr)
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
        elif bytes_stdout:
            query.setQueryResponseSize(len(bytes_stdout))
            query.setQueryResponse(bytes_stdout, bytes_stderr)
            query.setQueryStatus(status)
        else:
            if bytes_stderr:
                resp_gzip = self.gzipCompress('')
                query.setQueryResponseSize(len(resp_gzip))
                query.setQueryResponse(resp_gzip, bytes_stderr)
            elif ssh_exception:
                query.setQueryResponseSize(len(ssh_exception))
                query.setQueryResponse(ssh_exception)
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)

        query_end_time = int(round(time.time() * 1000))
        query.setQueryResponseTime(query_end_time - query_start_time)


    def queryVCenter(self, vcenter_client, node_id, query):
        max_retries = 2
        query_id = query.getQueryId()
        cmd = query.getQueryCmd()
        resp = None
        err = None
        query_start_time = 0
        query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
        while max_retries > 0:
            try:
                self.logger.info(
                    "NodeId: %d, Querying: %s" %
                    (node_id, query_id))
                query_start_time = int(round(time.time() * 1000))
                query.setQueryTimeMillis(query_start_time)
                resp = vcenter_client.runQuery(query_id, cmd)
                break
            except Exception as e:
                err = str(e)
                if max_retries == 1:
                    self.logger.warning(
                    ("May be due to timeout while running query : %s will retry"
                     "one more time and Error details are %s" %
                     (query_id, err)))
                max_retries -= 1

        if resp is not None:
            resp_txt = str(resp)
            query.setQueryResponse(self.gzipCompress(resp_txt))
            query.setQueryResponseSize(len(resp_txt))
            query.setQueryStatus(GenericQueryResult.QueryStatus.SUCCESS)
        else:
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            query.setQueryResultError(err)
        query_end_time = int(round(time.time() * 1000))
        query.setQueryResponseTime(query_end_time - query_start_time)

    def queryNetScaler(self, netscaler_client, node_id, query):
        max_retries = 2
        query_id = query.getQueryId()
        cmd = query.getQueryCmd()
        resp = None
        err = None
        query_start_time = 0

        query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
        while max_retries > 0:
            try:
                self.logger.info(
                    "NodeId: %d, Querying: %s" %
                    (node_id, query_id))
                query_start_time = int(round(time.time() * 1000))
                query.setQueryTimeMillis(query_start_time)
                resp = netscaler_client.runQuery(query_id, cmd)
                break
            except Exception as e:
                err = str(e)
                if max_retries == 1:
                    self.logger.warning(
                    ("May be due to timeout while running query : %s will retry"
                     "one more time and Error details are %s" %
                     (query_id, err)))
                max_retries -= 1

        if resp is not None:
            query.setQueryResponse(self.gzipCompress(resp))
            query.setQueryResponseSize(len(resp))
            query.setQueryStatus(GenericQueryResult.QueryStatus.SUCCESS)
        else:
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            query.setQueryResultError(err)
        query_end_time = int(round(time.time() * 1000))
        query.setQueryResponseTime(query_end_time - query_start_time)

    def queryF5LB(self, f5_client, node_id, query):
        max_retries = 2
        query_id = query.getQueryId()
        cmd = query.getQueryCmd()
        resp = None
        err = None
        query_start_time = 0

        query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
        while max_retries > 0:
            try:
                self.logger.info(
                    "F5 NodeId: %d, Querying: %s" %
                    (node_id, query_id))
                query_start_time = int(round(time.time() * 1000))
                query.setQueryTimeMillis(query_start_time)
                resp = f5_client.runQuery(query_id, cmd)
                break
            except Exception as e:
                err = str(e)
                if max_retries == 1:
                    self.logger.warning(
                        ("May be due to timeout while running query : %s will retry"
                         "one more time and Error details are %s" %
                         (query_id, err)))
                max_retries -= 1

        if resp is not None:
            query.setQueryResponse(self.gzipCompress(resp))
            query.setQueryResponseSize(len(resp))
            query.setQueryStatus(GenericQueryResult.QueryStatus.SUCCESS)
        else:
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            query.setQueryResultError(err)
        query_end_time = int(round(time.time() * 1000))
        query.setQueryResponseTime(query_end_time - query_start_time)

    def emitOrSaveQueryResult(self, query):
        if not self.continue_collecting:
            error_message = COLLECTION_ABORTED_STR%("emit/save of",
                                                    query.getQueryCmd())
            raise GenericCollector.CollectionAbortedException(error_message)
        if self.call_back is not None:
            self.call_back(query)
        else:
            self.saveResults(query)

    def computePerNodeJobs(self):
        self.total_query_count = 0
        for each_node in self.node_jobs:
            queries = self.getQueriesPerNode(each_node)

            self.total_query_count = self.total_query_count + len(queries)
            self.jobs.append((each_node, queries, self.user, self.password,
                              self.protocol, self.port, self.lan_username, self.lan_password, self.leaf_list))

    def createQuery(self, node, query):
        query.setNode(node)
        return query

    def gzipCompress(self, result):
        out = io.BytesIO()
        '''
        VIV note for gzip.GzipFile:
            * py2: fileobj can be io.BytesIO or io.StringIO or StringIO.StringIO
            * py3: fileobj screams if it is io.StringIO
            * will specify fileobj to be io.BytesIO -> this also requires
                result (rsp_text) to be in bytes and not converted to string
        '''
        with gzip.GzipFile(fileobj=out, mode="w", compresslevel=1) as f:
            if not isinstance(result, bytes):
                result = result.encode("utf-8")
            f.write(result)
        return out.getvalue()
        # return zlib.compress(result, 1)

    def gzipCompressRaw(self, result):
        out = io.BytesIO()
        count = 0
        with gzip.GzipFile(fileobj=out, mode="w", compresslevel=1) as f:
            for line in result.iter_content(chunk_size=10000):# 10 KB Chunks
                count += len(line)
                f.write(safely_encode_str(line))
        return (out.getvalue(), count)

    '''
    Compute queries for each type of node : APIC/Switch/Spine
    '''
    def getQueriesPerNode(self, node):
        queries = []
        if self.exclude_all_queries == True:
            return []
        if node.node_role == CONTROLLER:
            for query in self.LogicalQueries.getTopologyApicQueries():
                queries.append(self.createQuery(node, query))
            # Following queries only need to be executed on one apic node
            node_apic_queries = []
            for query in self.LogicalQueries.getApicQueries(self):
                node_apic_queries.append(self.createQuery(node, query))
            if self.passesFilter(
                    QueryId.LOGICAL_TENANT):  # just an optimization
                for query in self.LogicalQueries.getPerTenantQueries(
                        self, node):
                    node_apic_queries.append(self.createQuery(node, query))
            if self.passesFilter(QueryId.LOGICAL_AUDITLOGS):
                query = self.LogicalQueries.createAuditQuery(self.logger, node.getTime())
                if query:
                    node_apic_queries.append(self.createQuery(node, query))
            # Filter by hash for this collector
            total_apic_count = len(self.node_controller)
            node_index = self.node_controller.index(node)
            for k in range(0, len(node_apic_queries)):
                if (k % total_apic_count) == node_index:
                    queries.append(node_apic_queries[k])
        elif node.node_role in [LEAF, SPINE]:
            for query in self.SwitchQueries.getQueries(
                    self,
                    node.node_asic_type,
                    node.node_role,
                    node.node_fcs,
                    node.node_intf_list):
                queries.append(self.createQuery(node, query))
        elif node.node_role == VCENTER:
            for query in self.VCenterQueries.getQueries():
                queries.append(self.createQuery(node, query))
        elif node.node_role == NETSCALER:
            netScalerQueries, netscalerQueryIds = self.NetScalerQueries.getQueries()
            for query in netScalerQueries:
                queries.append(self.createQuery(node, query))
        elif node.node_role == F5:
            f5queries, f5QueryIds = self.F5Queries.getQueries()
            # Filter queries
            for query in f5queries:
                queries.append(self.createQuery(node, query))
        elif node.node_role in [STANDALONE_LEAF, STANDALONE_SPINE]:
            for query in self.StandaloneQueries.getQueries(node.node_role,
                                                           node.getSaFabric()):
                queries.append(self.createQuery(node, query))
            #if self.passesFilter(QueryId.NX_FABRIC_SHOW_IP_ARP_VRF) and node.node_role == STANDALONE_LEAF:
                #for vrf_query in self.StandaloneQueries.getPerVrfQueries(self, node):
                    #queries.append(self.createQuery(node, vrf_query))
            if self.passesFilter(QueryId.NX_FABRIC_VPC_CONSISTENCY_INTERFACE) and node.node_role == STANDALONE_LEAF:
                for vpc_query in self.StandaloneQueries.getVpcInterfaceConsistencyQueries(self, node):
                    queries.append(self.createQuery(node, vpc_query))
        elif node.node_role == DCNM:
            for query in self.StandaloneQueries.getQueries(node.node_role,
                                                           node.getSaFabric(),
                                                           node.getVersion()):
                queries.append(self.createQuery(node, query))

            # inventory query is part of creating inband query,
            # so add it to query list if not creating inband query
            if node.getLoopbackInterface() >= 0 and self.passesFilter(QueryId.NX_FABRIC_DCNM_GLOBAL_INTERFACE):
                inb_query = self.StandaloneQueries.createStandaloneInbQuery(self, node)
                if inb_query:
                    queries.append(self.createQuery(node, inb_query))
            else:
                inv_query = self.StandaloneQueries.getInventoryQuery(node.getSaFabric(), node.getVersion())
                queries.append(self.createQuery(node, inv_query))
        elif node.node_role == MSO:
            node_mso_queries = []
            for query in self.MsoQueries.getQueries():
                node_mso_queries.append(self.createQuery(node, query))

            if self.passesFilter(QueryId.MSO_POLICY_REPORT):
                mso_policy_report_queries = self.MsoQueries.getMsoPolicyReportQuery(self, node)
                if mso_policy_report_queries is not None:
                    for policy_report_query in mso_policy_report_queries:
                        node_mso_queries.append(self.createQuery(node, policy_report_query))

            good_mso_nodes = [x for x in self.node_controller if x.isMso() and x.node_is_login is True]
            total_mso_count = len(good_mso_nodes)
            good_mso_nodes.sort(key=lambda x:x.node_ip)
            if node in good_mso_nodes:
                node_index = good_mso_nodes.index(node)
                for k in range(0, len(node_mso_queries)):
                    if (k % total_mso_count) == node_index:
                        queries.append(node_mso_queries[k])
        else:
            self.logger.warning("Unknown role detected for a fabric node :%s "
                               % (node.node_role))
        # Filter queries
        filtered_queries = []
        for query in queries:
            if self.passesFilter(query.getQueryId()):
                filtered_queries.append(query)
        return filtered_queries


'''
Implement ACI Config Export functionality

Do we need an export timeout ?
Using node timeout for now

'''


class ApicExportConfigurationCollector(GenericCollector):

    def __init__(self, logger,
                 user, password,
                 export_policy_name,
                 export_policy_format="xml",
                 export_policy_time_out=600,
                 apic_login_time_out=20,
                 apic_query_time_out=240,
                 apic_node_time_out=600,
                 call_back=None):

        GenericCollector.__init__(self, logger, user, password, 0, 1,
                                  apic_login_time_out, apic_query_time_out,
                                  export_policy_time_out, max_threads=1,
                                  call_back=call_back)

        self.logger = logger
        self.export_policy_name = export_policy_name
        self.export_policy_format = export_policy_format
        self.export_policy_time_out = export_policy_time_out
        self.node = None
        # key = QueryId, value=Query object
        self.export_query_id_map = {}
        self.rest_access = None
        self.ssh_access = None


        self.export_policy_dn = None
        self.export_job_filename = None
        self.trigger_date_time = None
        self.export_results = []
        self.remote_path = self.LogicalQueries.ApicConfigExportPolicy.getRemotePath(self)
        self.node_collection_stats = None
        self.trigger_date_time = None
        self.snapshot_job_dn = None
        self.config_job_dn = None
        # TODO: Add assert to check for only apic
        # max threads = 1

    def setTopoNodeList(self, node_list):
        GenericCollector.setTopoNodeList(self, node_list)
        self.node = self.node_controller[0]
        # so queries are not split among multiple APICs
        self.node_controller = [self.node]

    def getAndUpdateCollectionTime(self):
        return GenericCollector.getAndUpdateCollectionTime(self, self.node_collection_stats,
                                                           self.export_policy_time_out)

    def is_threadpool_active(self):
        return False

    def increment_job_count(self):
        self.job_count += 1

    def initializeConnection(self, node):
        return GenericCollector.initializeConnection(self, node, self.user,
            self.password, self.protocol, self.port, self.node_collection_stats)

    def process(self):
        try:
            self.collectNodeQueries()
        except Exception as e:
            self.logger.warning(
                "Apic config export collection *FAILED* reason:%s" %
                str(e))

    def initConfigExportQueries(self):
        # APIC config export policy
        self.setFilterQueryIds(FilterQueryIds.getConfigExportQueryIds())
        for each_query in self.getQueriesPerNode(self.node):
            self.export_query_id_map[each_query.query_id] = each_query

    # This function implements function similar to that in GenericCollector
    # Is single threaded
    def collectNodeQueries(self):
        self.initConfigExportQueries()
        # Init stats for collector
        self.node_collection_stats = NodeCollectionStats(
            self.logger, self.node, len(self.export_query_id_map),
            round(time.time()))
        (self.rest_access,
         self.ssh,
         vcenter_unused,
         netsclaer_unused,
         f5_unused) = self.initializeConnection(self.node)

        # Export queries to be issued in this order
        ordered_query_ids = [QueryId.LOGICAL_CONFIG_EXPORT_POLICY,
                             QueryId.LOGICAL_CONFIG_EXPORT_POLICY_ID,
                             QueryId.LOGICAL_CONFIG_EXPORT_STATUS,
                             QueryId.LOGICAL_CONFIG_EXPORT_COPY,
                             QueryId.LOGICAL_CONFIG_EXPORT_DELETE_SNAPSHOT,
                             QueryId.LOGICAL_CONFIG_EXPORT_DELETE_JOB]

        for query_id in ordered_query_ids:
            query = self.export_query_id_map[query_id]
            collection_time_remaining = self.getAndUpdateCollectionTime()
            if not self.continue_collecting:
                err_msg = "Collection has been aborted, skipping query : %s"%(
                            query.getQueryCmd())
                raise CollectionAbortedException(err_msg)
            elif collection_time_remaining > self.query_time_out:
                self.increment_job_count()
                if query_id == QueryId.LOGICAL_CONFIG_EXPORT_POLICY:
                    self.createConfigExportPolicy(query)
                elif query_id == QueryId.LOGICAL_CONFIG_EXPORT_POLICY_ID:
                    self.getConfigExportId(query)
                elif query_id == QueryId.LOGICAL_CONFIG_EXPORT_STATUS:
                    self.checkConfigExportStatus(query)
                elif query_id == QueryId.LOGICAL_CONFIG_EXPORT_COPY:
                    self.remoteCopyConfigExportTarGz(query)
                elif query_id == QueryId.LOGICAL_CONFIG_EXPORT_DELETE_SNAPSHOT:
                    self.deleteConfigExportTarGz(query)
                elif query_id == QueryId.LOGICAL_CONFIG_EXPORT_DELETE_JOB:
                    self.deleteConfigExportJob(query)
            else:
                self.logger.warning(
                    "Node: %d, Collection time out triggered, skipping query : %s" %
                    (self.node.node_id, query.getQueryCmd()))
                query.setQueryResponseSize(len(NODE_TIMEOUT_STR))
                query.setQueryResponse(self.gzipCompress(NODE_TIMEOUT_STR))
                query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)

            self.emitOrSaveQueryResult(query)
            self.node_collection_stats.setFailedQuery(query)

    def createConfigExportPolicy(self, query):
        export_policy_config = str(self.LogicalQueries.ApicConfigExportPolicy.getPolicyTemplate(self).substitute(
            export_name=self.export_policy_name,
            export_format=self.export_policy_format,
            user=self.user,
            password=self.password))
        query.setQueryData(export_policy_config)
        self.queryRest(self.rest_access, self.node, query)
        if query.getQueryStatus() == GenericQueryResult.QueryStatus.SUCCESS:
            self.logger.info("Apic config export configuration *SUCCEEDED*")
        else:
            reason, _ = query.getQueryResponse()
            self.logger.warning(
                "Apic config export configuration *FAILED* , Reason:%s" %
                (GlobalUtils.gzipDecompress(self,reason)))

    def getConfigExportId(self, query):
        if not self.export_query_id_map[QueryId.LOGICAL_CONFIG_EXPORT_POLICY].isSuccess(
        ):
            self.logger.warning(
                "Not checking policy id, since export policy is *NOT* configured")
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            query.setQueryResponseSize(len(CONFIG_EXPORT_POLICY_NOT_CONFIGURED))
            query.setQueryResponse(
                self.gzipCompress(CONFIG_EXPORT_POLICY_NOT_CONFIGURED))
        else:
            #modTs takes time for updation,
            time.sleep(20)
            self.export_policy_dn = str(self.LogicalQueries.ApicConfigExportPolicy.getExportDnTemplate(self).substitute(export_name=self.export_policy_name))
            self.export_policy_cont_dn  = str(self.LogicalQueries.ApicConfigExportPolicy.getConfigJobContDnTemplate(
                self).substitute(export_dn=self.export_policy_dn))

            # LookupbyDn of configExportPolicy
            query.setQueryCmd('/api/mo/' + self.export_policy_cont_dn + ".xml")
            self.queryRest(self.rest_access, self.node, query)
            if query.getQueryStatus() == GenericQueryResult.QueryStatus.SUCCESS:
                response, _ = query.getQueryResponse()
                query_response = GlobalUtils.gzipDecompress(self, response)
                config_export_container_elements = ParseUtils.findAll(
                    self, query_response, "configJobCont")
                if config_export_container_elements:
                    self.trigger_date_time = ParseUtils.getAttribute(
                        self, config_export_container_elements[0], "lastJobName")
            else:
                reason, err = query.getQueryResponse()
                self.logger.warning(
                    "Apic config export id computation *FAILED* , Reason:%s" %
                    (GlobalUtils.gzipDecompress(self, reason)))


    def checkConfigExportStatus(self, query):
        if not self.export_query_id_map[QueryId.LOGICAL_CONFIG_EXPORT_POLICY_ID].isSuccess(
        ):
            self.logger.warning(
                "Not checking policy status, since export policy trigger time is *NOT* configured")
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            query.setQueryResponseSize(len(CONFIG_EXPORT_POLICY_ID_NOT_CONFIGURED))
            query.setQueryResponse(
                self.gzipCompress(CONFIG_EXPORT_POLICY_ID_NOT_CONFIGURED))
            return

        if self.export_policy_dn and self.trigger_date_time:
            retry_status_check_count = self.getAndUpdateCollectionTime()/CONFIG_EXPORT_RETRY_INTERVAL
            retry = True
            while retry_status_check_count > 0 and retry is True:
                if not self.continue_collecting:
                    raise CollectionAbortedException()
                # Sleeping first since, in experiments, we always have to retry.
                # To avoid retry , delay candid polling by sleep interval,
                # to  give apic time to finish doing configuration export
                time.sleep(CONFIG_EXPORT_RETRY_INTERVAL)
                config_job_dn_t = self.LogicalQueries.ApicConfigExportPolicy.getConfigJobDnTemplate(
                    self)
                snapshot_job_dn_t = self.LogicalQueries.ApicConfigExportPolicy.getSnapshotJobDnTemplate(
                    self)
                self.config_job_dn = str(config_job_dn_t.substitute(export_dn=self.export_policy_dn,
                                                                run_time=self.trigger_date_time))
                self.snapshot_job_dn = str(snapshot_job_dn_t.substitute(export_dn=self.export_policy_dn,
                                                                run_time=self.trigger_date_time))
                query.setQueryCmd('/api/mo/' + self.config_job_dn + ".xml")
                self.queryRest(self.rest_access, self.node, query)
                if query.getQueryStatus() == GenericQueryResult.QueryStatus.SUCCESS:
                    # Lookup configJob corresponding to config export
                    # if the job status is not sucess, and not failure, retry after sometime
                    # If success , get the file name to scp
                    response, _ = query.getQueryResponse()
                    query_response = GlobalUtils.gzipDecompress(self, response)
                    config_job_element = ParseUtils.findAll(
                        self, query_response, "configJob")
                    if config_job_element:
                        oper_state = ParseUtils.getAttribute(
                            self, config_job_element[0], "operSt")
                        if oper_state.lower() == "success":
                            self.export_job_filename = ParseUtils.getAttribute(
                                self, config_job_element[0], "fileName")
                            retry = False
                            break
                        elif oper_state.lower() == "running" or oper_state.lower() == "pending":
                            self.logger.warning(
                                "Config export still running retrying...retry_count %d"%retry_status_check_count)
                        else:
                            self.logger.warning(
                                "Config export *FAILED* oper_state validation oper_state:%s" %
                                (oper_state))
                            break
                else:
                    reason, err = query.getQueryResponse()
                    self.logger.warning(
                        "Apic config export configuration *FAILED* , Reason:%s" %
                        (GlobalUtils.gzipDecompress(self, reason)))
                retry_status_check_count = retry_status_check_count - 1

    # SFTP .tar.gz from APIC
    # TODO: If copy and delete fails , generate Assurance control event-
    def remoteCopyConfigExportTarGz(self, query):
        if self.export_job_filename is None:
            self.logger.warning(
                "Nothing to copy from APIC , since export policy status is not *succcess*")
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            query.setQueryResponseSize(len(CONFIG_EXPORT_POLICY_STATUS_NOT_SUCCESS))
            query.setQueryResponse(
                self.gzipCompress(CONFIG_EXPORT_POLICY_STATUS_NOT_SUCCESS))
            return

        # Set the file path to be copied from the previous set
        if self.export_job_filename and self.remote_path:
            query.setQueryParamRemotePath(
                self.remote_path + self.export_job_filename)
            query.appendQueryCmd(self.export_job_filename)

            # check each apic for config export
            for current_node in self.topo_node_list:
                current_ssh = None
                if current_node.getNodeIp() == self.node.getNodeIp():
                    current_ssh = self.ssh
                else:
                    current_ssh = self.initializeConnection(current_node)[1]

                if current_ssh:
                    self.querySftp(current_ssh, current_node, query)
                    if query.isSuccess():
                        query.setNode(current_node)
                        break;

    def deleteConfigExportTarGz(self, query):
        if not self.export_job_filename:
            self.logger.warning(
                "Not deleting snapshot file from APIC , since export policy status is not *succcess*")
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            query.setQueryResponseSize(len(CONFIG_EXPORT_POLICY_STATUS_NOT_SUCCESS))
            query.setQueryResponse(
                self.gzipCompress(CONFIG_EXPORT_POLICY_STATUS_NOT_SUCCESS))
            return

        query.setQueryCmd('/api/node/mo/' + self.snapshot_job_dn + ".xml")
        delete_snapshot_config = str(self.LogicalQueries.ApicConfigExportPolicy.getDeleteSnapshotTemplate(self).substitute(
            snapshot_job_dn=self.snapshot_job_dn))
        query.setQueryData(delete_snapshot_config)

        self.queryRest(self.rest_access, self.node, query)
        if query.getQueryStatus() == GenericQueryResult.QueryStatus.SUCCESS:
            self.logger.info("Deleted snapshot file on Apic")
        else:
            reason, _ = query.getQueryResponse()
            self.logger.warning(
                "Unable to delete snapshot file on Apic, Reason:%s" %
                (GlobalUtils.gzipDecompress(self, reason)))

    def deleteConfigExportJob(self, query):
        if not self.export_query_id_map[QueryId.LOGICAL_CONFIG_EXPORT_DELETE_SNAPSHOT].isSuccess(
        ):
            # will not delete config job if snapshot file is not deleted to retain information
            self.logger.warning(
                "Not deleting policy export job since snapshot was not deleted successfully")
            query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)
            query.setQueryResponseSize(len(CONFIG_EXPORT_SNAPSHOT_NOT_DELETED))
            query.setQueryResponse(
                self.gzipCompress(CONFIG_EXPORT_SNAPSHOT_NOT_DELETED))
            return

        query.setQueryCmd('/api/mo/' + self.export_policy_dn + ".xml")
        delete_policy_config = str(self.LogicalQueries.ApicConfigExportPolicy.getDeleteExportConfigTemplate(self).substitute(
            export_policy_dn=self.export_policy_dn))
        query.setQueryData(delete_policy_config)

        self.queryRest(self.rest_access, self.node, query)
        if query.getQueryStatus() == GenericQueryResult.QueryStatus.SUCCESS:
            self.logger.info("Deleted config export on Apic")
        else:
            reason, _ = query.getQueryResponse()
            self.logger.warning(
                "Unable to delete config export on Apic, Reason:%s" %
                (GlobalUtils.gzipDecompress(self, reason)))



    def getExportJobFileName(self):
        return self.export_job_filename

    def getQueryResults(self):
        return self.results

'''
Implement SSH command executor functionality

'''


class CommandExecutor(GenericCollector):

    def __init__(self, logger,
                 user, password,
                 commands=[],
                 login_time_out=20,
                 query_time_out=240,
                 node_time_out=600,
                 call_back=None,
                 ):

        GenericCollector.__init__(self, logger, user, password, 0, 1,
                                  login_time_out, query_time_out,
                                  node_time_out, max_threads=1,
                                  call_back=call_back)

        self.logger = logger
        self.node = None
        # key = QueryId, value=Query object
        self.command_query_list = []
        self.rest_access = None
        self.ssh_access = None
        self.commands = commands;

        self.export_policy_dn = None
        self.export_job_filename = None
        self.trigger_date_time = None
        self.export_results = []
        self.node_collection_stats = None
        self.trigger_date_time = None


    def setExecuteNodeList(self, node_list):
        [x.setNodeRole(COMMAND_NODE) for x in node_list]
        self.topo_node_list =  node_list

    def getAndUpdateCollectionTime(self):
        return GenericCollector.getAndUpdateCollectionTime(self, self.node_collection_stats,
                                                           self.node_time_out)

    def is_threadpool_active(self):
        return False

    def initializeConnection(self, node):
        return GenericCollector.initializeConnection(self, node, self.user,
                                                     self.password, self.protocol, self.port, self.node_collection_stats)

    def process(self):
        try:
            for node in self.topo_node_list:
                self.executeSshCommands(node)
        except Exception as e:
            trace = ExceptionUtils.createTraceback(traceback.format_stack())
            self.logger.warning(
                "Command execution *FAILED* reason:%s" %
                str(e))

    def getExecutionCommandQueries(self, node):
        # Custom command queries
        query_list = []
        for each_command in self.commands.get(node.getNodeIp(), []):
            command = each_command.get("command")
            if command:
                # using unknown query id here until 5000 query id is put in ucs.proto
                query = SshQuery(QueryId.UNKNOWN_QUERY_ID, command, False, True)
                query.setNode(node)
                query_list.append(query);
        return query_list

    # This function implements function similar to that in GenericCollector
    # Is single threaded
    def executeSshCommands(self, node):
        query_list = self.getExecutionCommandQueries(node)
        if not query_list:
            self.logger.warning("No queries found for ip: %s, name: %s"%(
                node.getNodeIp(), node.getNodeName()))
            return;

        # Init stats for collector
        self.logger.info("Initialized commands ")
        self.logger.info("initializing nodeCollection stats")
        self.node_collection_stats = NodeCollectionStats(
            self.logger, node, len(query_list),
            round(time.time()))

        (rest_access,
         ssh,
         vcenter_unused,
         netsclaer_unused,
         f5_unused) = self.initializeConnection(node)
        self.logger.info("Initialized the connections ")
        try:

            for query in query_list:
                self.logger.info("executing query")
                collection_time_remaining = self.getAndUpdateCollectionTime()
                if not self.continue_collecting:
                    err_msg = "Command Execution has been aborted, skipping query : %s"%(
                        query.getQueryCmd())
                    raise ExecutionAbortedException(err_msg)
                elif collection_time_remaining > self.query_time_out:
                    if query.getQueryType() == GenericQueryResult.QueryType.SSH:
                        self.querySsh(ssh, node, query, self.query_time_out)
                else:
                    self.logger.warning(
                        "Node: %d, Command Execution time out triggered, skipping query : %s" %
                        (node.node_id, query.getQueryCmd()))
                    query.setQueryResponseSize(len(NODE_TIMEOUT_STR))
                    query.setQueryResponse(self.gzipCompress(NODE_TIMEOUT_STR))
                    query.setQueryStatus(GenericQueryResult.QueryStatus.FAIL)

                self.emitOrSaveQueryResult(query)
                self.node_collection_stats.setFailedQuery(query)
        except Exception as e:
            self.logger.error(
                "Exception while executing command : %s, Line Number: %s Reason: %s" %
                (query.getQueryCmd(), sys.exc_info()[2].tb_lineno, str(e)))
        finally:
            try:
                if rest_access:
                    rest_access.logout()
                if ssh:
                    ssh.close()
            except Exception as e:
                self.logger.debug(
                    "Exception while closing the sessions on node:%s Reason: %s"
                    %(node.node_id, str(e)))


    def getQueryResults(self):
        return self.results

class ProcessResults():
    def __init__(self, logger=None, ccg = None, topo_node_list=None,
                 target_dir=None, results=None, collection_time=None):
        self.logger = logger
        self.ccg = ccg
        self.topo_node_list = topo_node_list
        self.target_dir = target_dir
        self.results = results
        self.collection_time = collection_time
        self.write_output_results()

    def write_output_results(self):
        current_dir = os.getcwd()
        os.chdir(self.target_dir)
        #Add configuration options to output directory
        #Every epoch should have configuration options since they can be different in the online mode
        self.ccg.createJson()
        for each_node in self.topo_node_list:
            # Skip nodes that have invalid node ids
            if each_node.node_id == 0 or each_node.node_is_login == False:
                continue
            output_dir = './node-' + str(each_node.node_id)
            try:
                os.makedirs(output_dir)
            except OSError:
                raise CandidDataCollectionException(
                    "Output target directory create FAILED: " + str(output_dir))
        f = open('topology.json', 'w')
        topology_json = {}
        topology_json.update(
            {"offline_version": GlobalUtils.getVersion(
                self.logger, current_dir,
                self.ccg.get("versionProperties"))})
        if self.collection_time is not None:
            topology_json.update({"collection_time": self.collection_time})
        topo_nodes = {"nodes": []}
        for each_topo_node in self.topo_node_list:
            node_dict = dict(each_topo_node.__dict__)
            node_dict["node_admin_config"] = node_dict.get("node_admin_config", b"").decode("utf-8")
            if 'node_asic_type' in node_dict:
                del node_dict['node_asic_type']
            connection_info_list = []
            for connection_info in each_topo_node.node_connection_info:
                connection_info_list.append(connection_info.__dict__)
            node_dict["node_connection_info"] = connection_info_list
            topo_nodes["nodes"].append(node_dict)
        topology_json.update(topo_nodes)
        f.write(json.dumps(topology_json, sort_keys=True, indent=4))
        f.close()

        # Number of results = # of nodes
        node_to_jsonlist_dict = {}
        for each_query_result in self.results:
            cwd = os.getcwd()
            node = each_query_result.getNode()
            if node.node_id == 0:
                for topo_node in self.topo_node_list:
                    try:
                        if topo_node.node_ip == node.node_ip:
                            node.node_id = topo_node.node_id
                            break
                    except BaseException:
                        print("Invalid node id for topo-node: " + \
                            str(topo_node))
            output_dir = './node-' + str(node.node_id)
            try:
                os.chdir(output_dir)
            except BaseException:
                self.logger.warning(
                    "Unable to change directory to: " +
                    str(output_dir))
                continue

            query = each_query_result.getQueryCmd()
            queryId = QueryIdToString.getQueryName(each_query_result.getQueryId())
            rsp, err = each_query_result.getQueryResponse()
            query_result_status = each_query_result.getQueryStatusString()
            if node.node_id not in node_to_jsonlist_dict:
                node_to_jsonlist_dict[node.node_id] = []
            if each_query_result.getQueryType() == GenericQueryResult.QueryType.SSH:
                temp_file_name = self.genTempFile('.stdout.gz', rsp)
                rslt_dict = {'query': query,
                             'queryStatus': query_result_status,
                             'file': temp_file_name,
                             'queryId': queryId}
                node_to_jsonlist_dict[node.node_id].append(rslt_dict)
                if err is not None:
                    temp_file_name = self.genTempFile('.stderr.gz', err)
                    rslt_dict = {'query': query,
                                 'queryStatus': query_result_status,
                                 'file': temp_file_name,
                                 'queryId': queryId}
                    node_to_jsonlist_dict[node.node_id].append(rslt_dict)
            elif each_query_result.getQueryType() in [GenericQueryResult.QueryType.REST,
                                                      GenericQueryResult.QueryType.SFTP,
                                                      GenericQueryResult.QueryType.VCENTER,
                                                      GenericQueryResult.QueryType.NETSCALER,
                                                      GenericQueryResult.QueryType.F5_LB]:
                temp_file_name = self.genTempFile('.gz', rsp)
                rslt_dict = {'query': query,
                             'queryStatus': query_result_status,
                             'file': temp_file_name,
                             'queryId': queryId}
                node_to_jsonlist_dict[node.node_id].append(rslt_dict)
            os.chdir(cwd)
        for each_node_id in list(node_to_jsonlist_dict.keys()):
            cwd = os.getcwd()
            output_dir = './node-' + str(each_node_id)
            os.chdir(output_dir)
            f_hndl = open('command_map.json', 'w')
            f_hndl.write(
                json.dumps(
                    node_to_jsonlist_dict[each_node_id],
                    sort_keys=True,
                    indent=4))
            f_hndl.close()
            os.chdir(cwd)
        os.chdir(current_dir)

    def genTempFile(self, pfx, data):
        temp_file_name = next(tempfile._get_candidate_names())
        temp_file = open(temp_file_name + pfx, 'wb')
        if data is not None:
            temp_file.write(data)
        temp_file.close()
        return temp_file_name + pfx


class CandidException(Exception):
    pass


def loggerInit(output_dir=None, module_name='CnaeDataCollection'):
    import logging
    for each_module in ['requests', 'urllib3', 'paramiko', 'pyvmomi', 'nitro-python']:
        logging.getLogger(each_module).setLevel(logging.WARNING)

    format_pattern = '%(asctime)s %(name)-12s %(threadName)s %(levelname)-8s %(message)s'
    date_time_format = '%m-%d-%y %H:%M:%S'
    formatter = logging.Formatter(format_pattern, datefmt=date_time_format)

    # Create root logger
    logging.basicConfig(level=logging.INFO,
                        format=format_pattern,
                        datefmt=date_time_format,
                        stream=sys.stdout)

    if output_dir is not None:
        # Create a fileHandler for offline mode
        file_handler = logging.FileHandler(output_dir + '/candid.log')
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(formatter)
        logging.getLogger(module_name).addHandler(file_handler)
    else:
        # Create an error logger which writes ERROR messages to the sys.stderr
        error_handler = logging.StreamHandler()
        error_handler.setLevel(logging.ERROR)
        error_handler.setFormatter(formatter)
        logging.getLogger(module_name).addHandler(error_handler)

    return logging.getLogger(module_name)


def exitGracefully(logger):
    logger.warning(("Exiting Candid Data Collection Script"))
    raise SystemExit


'''
Code specific to offline data collection
'''


@candidTimeIt
def candidDataCollectionOffline(args, ccg=None):
    '''
    Create output directory
    '''
    try:
        # Creating configuration collector
        # delete logger stuff inside ccg
        # instantiate ccg AFTER log
        current_time = strftime("%Y-%m-%d_%H_%M_%S", gmtime())
        output_dir = ""

        if ccg:
            output_dir_name = ccg.get("clusterName") + '_' + current_time
            output_dir = ccg.get("targetDir") + '/' + output_dir_name
        else:
            output_dir_name = args.clusterName + '_' + current_time
            output_dir = args.targetDir + '/' + output_dir_name
        os.mkdir(output_dir)
        logger = loggerInit(output_dir)
        if ccg is None:
            ccg = CollectionConfigurationGenerator(logger, args.__dict__)
        sa_topo_args = None
        if ccg.get("cnaeMode") == _STANDALONE:
            sa_topo_args = StandaloneTopologyArgs(
                sa_fabric=ccg.get("siteName"),
                user=ccg.get("user"),
                dcnms=ccg.get("DCNM")
            )
            sa_topo_args.addStandaloneSpines(ccg.get("standaloneSpines"))
            sa_topo_args.addStandaloneLeafs(ccg.get("standaloneLeafs"))
            sa_topo_args.parseStandaloneInputTopology(ccg.get("standaloneInput"))
    except IOError as e:
        raise IOError(
            "I/O error({0}, may be due to incorrect permissions for writing data): {1}".format(
                e.errno, e.strerror))
    except OSError as e:
        raise OSError(
            "OS error({0}): {1}, destination directory :{2} already exists".format(
                e.errno, e.strerror, output_dir))
    else:
        '''
        APIC/STANDALONE/MSO Credentials
        '''
        try:
            print("Enter password for %s : %s , user: %s" % (
                ccg.get("cnaeMode"), ccg.get("entityIps"), ccg.get("user")))
            password = getpass.getpass()
        except Exception as e:
            raise SystemExit("Please enter password:" + str(e))

        # Ask for lan password only if the mode is standalone
        lan_password = None
        if ccg.get("cnaeMode") == _STANDALONE:
            try:
                print("Enter default LAN password for %s : %s , LAN user: %s" % (
                    ccg.get("cnaeMode"), ccg.get("entityIps"), ccg.get("lanUsername")))
                lan_password = getpass.getpass(prompt='Default LAN Password:')
            except Exception as e:
                raise SystemExit("Please enter LAN password:" + str(e))
        leaf_list = {}
        leaf_cred_overwrite = ccg.get("leafCredentialOverwrite")
        if leaf_cred_overwrite and leaf_cred_overwrite > 0:
            print("Enter IP address, User Name and Password for leaf switch to overwrite default credentials")
            for _ in range(ccg.get("leafCredentialOverwrite")):
                leaf_ip = six.moves.input("IP Address: ")
                leaf_unpw_data = {}
                un = six.moves.input('User Name: ')
                pw = getpass.getpass(prompt='Password for %s:' % (leaf_ip))
                leaf_unpw_data['userName'] = un
                leaf_unpw_data['passWord'] = pw
                leaf_list[leaf_ip] = leaf_unpw_data

        third_party_svc_ctx = ccg.get('thirdPartyServiceContext')

        '''
        Third-party services credentials
        '''
        try:
            ThirdPartyServicesAPI.readPasswords(third_party_svc_ctx)
        except Exception as e:
            raise SystemExit(str(e))

        logger.info("Checking for python module compatibility")
        version_check = candidCheckModuleVersion(logger, third_party_svc_ctx)
        if version_check is True:
            logger.info("Python module compatibility check *OK*")
        else:
            exitGracefully(logger)
        try:
            num_iterations = ccg.get("iterations")
            for each_epoch in range(1, num_iterations + 1):
                logger.info(
                    ("Collecting candid data sets iteration: %d" %
                     each_epoch))
                try:
                    collectPerEpochData(
                        ccg, password, output_dir, logger, each_epoch, lan_password, sa_topo_args, leaf_list)
                except CandidPartialDataCollectionException as e:
                    logger.warning(
                        "Data collection *PARTIAL* for iteration %d with exception message: %s",
                        each_epoch,
                        str(e))
                except Exception as e:
                    logger.info(
                        "Data collection *FAILED* for iteration %d with exception message: %s",
                        each_epoch,
                        str(e))
                else:
                    logger.info(
                        "Data collection *SUCCESSFUL*  for iteration: %d" %
                        each_epoch)
                if each_epoch < num_iterations:
                    logger.info(
                        ("Waiting for the next iteration, sleeping for %d sec..." %
                         (ccg.get("iterationIntervalSec"))))
                    time.sleep(ccg.get("iterationIntervalSec"))
        finally:
            processDataDir(logger, output_dir_name, ccg.get("targetDir"))
            logger.info("Exiting Candid Data collection")

def collectPerEpochData(ccg, password, output_dir, logger, iteration, lan_password=None, sa_topo_args=None, leaf_list=None):
    try:
        output_dir = output_dir + '/EPOCH-' + str(iteration)
        os.mkdir(output_dir)
    except IOError as e:
        raise IOError(
            "I/O error({0}, may be due to incorrect permissions for writing data): {1}".format(
                e.errno, e.strerror))
    except OSError as e:
        raise OSError(
            "OS error({0}): {1}, destination directory :{2} already exists".format(
                e.errno, e.strerror, output_dir))

    apic_ips = ccg.get("entityIps")
    user = ccg.get("user")
    apic_login_time_out = ccg.get("apicLoginTimeOut")
    apic_query_time_out = ccg.get("apicQueryTimeOut")
    apic_node_time_out = ccg.get("apicNodeTimeOut")
    dcnm_ips = []
    nat = None
    if ccg.get("nat") and ccg.getNatJsonEntries():
        nat = NatTranslator(logger, ccg.getNatJsonEntries())
    else:
        logger.info("No valid Nat Configuration file. Nat input: {0}".format(ccg.get("nat")))


    export_policy_name = ccg.get("apicConfigExportPolicyName")
    export_policy_format = ccg.get("apicConfigExportFormat")
    export_policy_timeout = ccg.get("apicConfigExportTimeOut")
    # nat = NatTranslator(logger, ccg.get("nat"))

    # TODO: Add protocol/port/requestFormat
    all_results = []
    version = []
    if ccg.get("cnaeMode") == _APIC:
        version = ccg.get("aciVersion")
    elif ccg.get("cnaeMode") == _MSO:
        version = ccg.get("msoVersion")
    else:
        version = ccg.get("dcnmVersion")
    try:
        topology_discovery = TopologyExplorer(
            logger=logger,
            apic_ips=apic_ips,
            user=user,
            password=password,
            apic_login_time_out=apic_login_time_out,
            apic_query_time_out=apic_query_time_out,
            apic_node_time_out=apic_node_time_out,
            request_format='xml',
            version=version,
            switch_version=ccg.get("switchVersion"),
            nat_box=nat,
            max_threads=ccg.get("maxThreads"),
            sa_topo_args=sa_topo_args,
            cnae_mode=ccg.get("cnaeMode"),
            lan_username=ccg.get("lanUsername"),
            lan_password=lan_password,
            leaf_list=leaf_list,
            loopback_interface=ccg.get("loopbackInterface"),
        )
        topology_discovery.setConnectionPreferencePrimary(ccg.get("connectionPreferencePrimary"))
        topology_discovery.setConnectionPreferenceSecondary(ccg.get("connectionPreferenceSecondary"))
        topology_discovery.process()
        all_results.extend(topology_discovery.getQueryResultsFromStash())
    except Exception as e:
        # TODO: Potentially get rid of exception below?
        raise CandidDataCollectionException(
            "Topology Discovery for fabric FAILED Reason: %s", str(e))

    else:
        try:
            all_nodes = []
            topo_node_list = topology_discovery.getTopoNodeList()
            all_nodes.extend(topo_node_list)
            controllers = [x for x in topo_node_list if x.isController() and
                                 x.node_quorum is True and
                                 x.node_is_login is True]
            if ccg.get("cnaeMode") == _APIC and not controllers:
                raise CandidDataCollectionException("Login failure on APICs or \
                             APICs are *NOT* fully-fit")
            else:
                if export_policy_name and export_policy_format and export_policy_timeout:
                    config_export = ApicExportConfigurationCollector(
                        logger,
                        user,
                        password,
                        export_policy_name,
                        export_policy_format,
                        export_policy_timeout,
                        apic_login_time_out,
                        apic_query_time_out,
                        apic_node_time_out,
                    )
                    config_export.setTopoNodeList(controllers)
                    config_export.process()
                    all_results.extend(config_export.getQueryResults())

                # collect ucs queries
                node_list = []
                filter_node_ids = ccg.get("filterNodeIds")
                if filter_node_ids:
                    node_list = [x for x in topo_node_list if x.node_id in filter_node_ids]
                if not node_list:
                    node_list = controllers + \
                        [x for x in topo_node_list if x.isLeaf() or
                         x.isSpine() or x.isStandaloneLeaf() or
                         x.isStandaloneSpine()] + \
                        [x for x in topo_node_list if x.isMso() and x.node_is_login is True]
                collector = GenericCollector(
                    logger,
                    ccg.get("user"),
                    password,
                    0,
                    1,
                    ccg.get("loginTimeOut"),
                    ccg.get("queryTimeOut"),
                    ccg.get("nodeTimeOut"),
                    ccg.get("apicLoginTimeOut"),
                    ccg.get("apicQueryTimeOut"),
                    ccg.get("apicNodeTimeOut"),
                    iteration=iteration,
                    max_threads=ccg.get("maxThreads"),
                    cnae_mode=ccg.get("cnaeMode"),
                    lan_username=ccg.get("lanUsername"),
                    lan_password=lan_password,
                    leaf_list=leaf_list)
                collector.setFilterQueryIds(ccg.get("queryIds"))
                collector.setExcludeQueryIds(
                FilterQueryIds.getTopologyExplorerQueryIds() + FilterQueryIds.getConfigExportQueryIds() + FilterQueryIds.getSupportedFeaturesQueryIdList() + FilterQueryIds.getMsoTopologyQueryIdList())
                collector.setTopoNodeList(node_list)
                collector.setOptimizedQuery(ccg.get("optimizedQuery"))
                legacy_mode = not ccg.get("noLegacyQuery")
                collector.setLegacyMode(legacy_mode)
                collector.process()
                all_results.extend(collector.getResults())

            svc_ctx = ccg.get('thirdPartyServiceContext')
            tp_topo_node_list = ThirdPartyServicesAPI.exploreTopology(svc_ctx)
            for topo_node in tp_topo_node_list:
                svc_dic = svc_ctx.getServiceDictionary(ThirdPartyServicesAPI.getNodeIp(topo_node))
                collector = GenericCollector(
                    logger,
                    svc_dic['user'],
                    svc_dic['password'],
                    0,
                    1,
                    ccg.get("loginTimeOut"),
                    ccg.get("queryTimeOut"),
                    ccg.get("nodeTimeOut"),
                    iteration=iteration,
                    max_threads=ccg.get("maxThreads"),
                    cnae_mode=ccg.get("cnaeMode"))
                collector.setFilterQueryIds(svc_dic['queryIds'])
                collector.setTopoNodeList([topo_node])
                collector.setLegacyMode(not ccg.get("noLegacyQuery"))
                collector.process()
                all_nodes.append(topo_node)
                all_results.extend(collector.getResults())

        except Exception as e:
            logger.error(
                ("Data collection FAILED Line Number: %s Reason:%s" %
                 (sys.exc_info()[2].tb_lineno, str(e))))
            traceback.print_stack()
            print('--------------')
            traceback.print_exc()
        else:
            for node in topo_node_list + tp_topo_node_list:
                if not node.isLoginSuccess():
                    raise CandidPartialDataCollectionException("Login was not successful on all nodes.")
        finally:
            try:
                results = ProcessResults(
                    logger,
                    ccg,
                    topo_node_list=all_nodes,
                    target_dir=output_dir,
                    results=all_results,
                    collection_time=int(
                        round(
                            time.time())))
            except Exception as e:
                logger.error(
                    ("FAILED to write data Line Number: %s Reason:%s" %
                     (sys.exc_info()[2].tb_lineno, str(e))))
                traceback.print_stack()
                print('--------------')
                traceback.print_exc()


def sizeOfFmt(num, suffix='B'):
    for unit in ['', 'K', 'M', 'G', 'T', 'P', 'E', 'Z']:
        if abs(num) < 1024.0:
            return "%3.1f%s%s" % (num, unit, suffix)
        num /= 1024.0
    return "%.1f%s%s" % (num, 'Yi', suffix)

# teach arcname


def processDataDir(logger, data_dir, target_dir):
    cwd = os.getcwd()
    os.chdir(target_dir)
    tar_file_name = data_dir + '.tar.gz'
    try:
        archive = tarfile.open(tar_file_name, "w|gz")
        archive.add(str(data_dir))
        size = sizeOfFmt(os.path.getsize(os.path.abspath(tar_file_name)))
        shutil.rmtree(str(data_dir), ignore_errors=True)
    except Exception as e:
        raise CandidException(
            "FAILED to compress/remove data directory, Reason: %s", str(e))
    else:
        logger.info(("Compressed data file located at : %s  size: %s" %
                     (os.path.abspath(tar_file_name), size)))
        os.chdir(cwd)
    finally:
        archive.close()


'''
Classes to implement session/request -get/post
Mostly adopted from cobra/but adapted to this script
'''


class AbstractSession(object):
    XML_FORMAT, JSON_FORMAT = 0, 1

    def __init__(self, controller_url, secure, timeout, request_format):
        if request_format not in {'xml', 'json'}:
            raise NotImplementedError("request_format should be one of: %s" %
                                      {'xml', 'json'})
        self.__secure = secure
        self.__timeout = timeout
        self.__controller_url = controller_url
        if request_format == 'xml':
            self.__format = AbstractSession.XML_FORMAT
        elif request_format == 'json':
            self.__format = AbstractSession.JSON_FORMAT

    @property
    def secure(self):
        """
        verifies server authenticity
        """
        return self.__secure

    @property
    def timeout(self):
        """
        communication timeout for the connection
        """
        return self.__timeout

    @property
    def url(self):
        return self.__controller_url

    @property
    def formatType(self):
        return self.__format

    @property
    def formatStr(self):
        return 'xml' if self.__format == AbstractSession.XML_FORMAT else 'json'

    def login(self):
        pass

    def logout(self):
        pass

    def refresh(self):
        pass


class AbstractRequest(object):
    """
    AbstractRequest is the base class for all other request types, including
    AbstractQuery, ConfigRequest, UploadPackage, LoginRequest and RefreshRequest
    """

    def __init__(self):
        self.__options = {}
        self.id = None
        self.__uriBase = ""

    @classmethod
    def makeOptions(cls, options):
        """
        Returns a string containing the concatenated values of all key/value
        pairs for the options defined in dict options
        """
        optionStr = ''
        if options:
            options = ['%s=%s' % (n, str(v)) if v else None
                       for n, v in list(options.items())]
            optionStr += '&'.join([_f for _f in options if _f])
        return optionStr

    def getUriPathAndOptions(self, session):
        return "%s.%s%s%s" % (self.uriBase,
                              session.formatStr,
                              '?' if self.options else '',
                              filterUrl(self.options))

    @property
    def options(self):
        """
        Return the HTTP request query string string for this object
        """
        return AbstractRequest.makeOptions(self.__options)

    # property setters / getters for this class

    @property
    def id(self):
        """
        Returns the id of this query if set, else None
        """
        return self.__options.get('_dc', None)

    @id.setter
    def id(self, value):
        """
        Sets the id of this query. The id is an internal troubleshooting
        value useful for tracing the processing of a request within the cluster
        """
        self.__options['_dc'] = value

    @property
    def uriBase(self):
        return self.__uriBase

    @uriBase.setter
    def uriBase(self, value):
        self.__uriBase = value

    def getUrl(self, session, url=None):
        """
        Returns the dn query URL containing all the query options defined on
        this object
        """
        return session.url + self.getUriPathAndOptions(session)

    def requestargs(self, session):
        return ""


class AbstractQuery(AbstractRequest):
    """
    Class representing an abstract query. The class is used by classQuery
    and Dnquery.
    """

    def __init__(self):
        super(AbstractQuery, self).__init__()
        self.__options = {}

    @property
    def options(self):
        """
        Returns the concatenation of the class and base class options for HTTP
        request query string
        """
        return '&'.join([_f for _f in [AbstractRequest.makeOptions(
            self.__options), super(AbstractQuery, self).options] if _f])

    # property setters / getters for this class

    @property
    def propInclude(self):
        """
        Returns the current response property include filter
        """
        return self.__options.get('rsp-prop-include', None)

    @propInclude.setter
    def propInclude(self, value):
        """
        Filters that can specify the properties that should be included in the
        response body
        """
        allowed_values = {'_all_', 'naming-only', 'config-explicit',
                          'config-all', 'config-only', 'oper'}
        if value not in allowed_values:
            raise ValueError('"%s" is invalid, valid values are "%s"' %
                             (value, str(allowed_values)))
        self.__options['rsp-prop-include'] = value

    @property
    def subtreePropFilter(self):
        """
        Returns the subtree prop filter.
        """
        return self.__options.get('rsp-subtree-filter', None)

    @subtreePropFilter.setter
    def subtreePropFilter(self, pFilter):
        """
        Returns the subtree prop filter.
        """
        self.__options['rsp-subtree-filter'] = str(pFilter)

    @property
    def subtreeClassFilter(self):
        """
        Returns the current subtree class filter.
        """
        return self.__options.get('rsp-subtree-class', None)

    @subtreeClassFilter.setter
    def subtreeClassFilter(self, value):
        """
        Returns the children of a single class.
        """
        if isinstance(value, list):
            value = ','.join(value)
        self.__options['rsp-subtree-class'] = value

    @property
    def subtreeInclude(self):
        """
        Returns the current subtree query values.
        """
        return self.__options.get('rsp-subtree-include', None)

    @subtreeInclude.setter
    def subtreeInclude(self, value):
        """
        Specifies optional values for a subtree query, including:
        *audit-logs
        *event-logs
        *faults
        *fault-records
        *ep-records
        *health
        *health-records
        *relations
        *stats
        *tasks
        *count
        *no-scoped
        *required
        *subtree
        """
        allowed_values = {
            'audit-logs',
            'event-logs',
            'faults',
            'fault-records',
            'ep-records',
            'health',
            'health-records',
            'deployment-records',
            'relations',
            'stats',
            'tasks',
            'count',
            'no-scoped',
            'required',
            'subtree'}
        all_values = value.split(',')
        for v in all_values:
            if v not in allowed_values:
                raise ValueError('"%s" is invalid, valid values are "%s"' %
                                 (value, str(allowed_values)))
        self.__options['rsp-subtree-include'] = value

    @property
    def queryTarget(self):
        """
        Returns the query type.
        """
        return self.__options.get('query-target', None)

    @queryTarget.setter
    def queryTarget(self, value):
        """
        Sets the query type. You can query the object (self), child objects
        (children), or all objects lower in the heirarchy (subtree).
        """
        allowed_values = {'self', 'children', 'subtree'}
        if value not in allowed_values:
            raise ValueError('"%s" is invalid, valid values are "%s"' %
                             (value, str(allowed_values)))
        self.__options['query-target'] = value

    @property
    def classFilter(self):
        """
        Returns the current class filter type.
        """
        return self.__options.get('target-subtree-class', None)

    @classFilter.setter
    def classFilter(self, value):
        """
        Filters by a specified class.
        """

        if isinstance(value, str):
            value = value.split(',')

        value = [name.replace('.', '') for name in value]
        value = ','.join(value)
        self.__options['target-subtree-class'] = value

    @property
    def propFilter(self):
        """
        Returns the current property filter type.
        """
        return self.__options.get('query-target-filter', None)

    @propFilter.setter
    def propFilter(self, pFilter):
        """
        Filters by a specified property value.
        """
        self.__options['query-target-filter'] = str(pFilter)

    @property
    def subtree(self):
        """
        Returns the current type of subtree filter.
        """
        return self.__options.get('rsp-subtree', None)

    @subtree.setter
    def subtree(self, value):
        """
        Filters query values within a subtree- you can filter by MOs (children)
        or return the entire subtree (full).
        """
        allowed_values = {'no', 'children', 'full'}
        if value not in allowed_values:
            raise ValueError('"%s" is invalid, valid values are "%s"' %
                             (value, str(allowed_values)))
        self.__options['rsp-subtree'] = value

    @property
    def replica(self):
        """
        Returns the current value for the replica option.
        """
        return self.__options.get('replica', None)

    @replica.setter
    def replica(self, value):
        """
        Direct the query to a specific replica
        """
        allowed_values = set([1, 2, 3])
        if value not in allowed_values:
            raise ValueError('"%s" is invalid, valid values are "%s"' %
                             (value, str(allowed_values)))
        self.__options['replica'] = value

    @property
    def orderBy(self):
        """Get the orderBy sort specifiers string.

        Returns:
          str: The order-by string of sort specifiers.
        """
        return self.__options.get('order-by', None)

    @orderBy.setter
    def orderBy(self, sort_specifiers):
        """Set the orderBy sort specifiers.

        Args:
          sort_specifiers (str or list of str): A list of sort specifier strings
            or a comma separated string of sort specifiers.
        """
        if isinstance(sort_specifiers, list):
            sort_specifiers = ','.join(sort_specifiers)
        self.__options['order-by'] = sort_specifiers

    @property
    def pageSize(self):
        """Get the page_size value.

        Returns:
          int: The number of results to be returned by a query.
        """
        return self.__options.get('page-size', None)

    @pageSize.setter
    def pageSize(self, page_size):
        """Set the page_size value.

        Args:
          page_size (int): The number of results to be returned by a query.
        """
        try:
            num_val = int(page_size)
        except BaseException:
            raise ValueError(
                '{} page_size needs to be an integer'.format(page_size))
        self.__options['page-size'] = str(num_val)

    @property
    def page(self):
        """Get the page value.

        Returns:
          int: The number of the page returned in the query.
        """
        return self.__options.get('page', None)

    @page.setter
    def page(self, value):
        """Set the page value.

        Args:
          page (int): The position in the query which should be retrieved.
        """
        try:
            num_val = int(value)
        except BaseException:
            raise ValueError('{} page needs to be an integer'.format(value))
        self.__options['page'] = str(num_val)

    @property
    def cacheId(self):
        return self.__options.get('cache-session', None)

    @cacheId.setter
    def cacheId(self, value):
        if value is None and 'cache-session' in self.__options:
            del self.__options['cache-session']
            return
        try:
            num_val = int(value)
        except BaseException:
            raise ValueError(
                '{} cache id needs to be an integer'.format(value))
        self.__options['cache-session'] = str(num_val)

    @property
    def deleteCacheId(self):
        return self.__options.get('delete-session', None)

    @deleteCacheId.setter
    def deleteCacheId(self, value):
        try:
            num_val = int(value)
        except BaseException:
            raise ValueError(
                '{} delete cache id needs to be an integer'.format(value))
        self.__options['delete-session'] = str(num_val)


class CompareQuery(object):
    # __cmp__ and cmp() is deprecated in python2

    def _compare(self, this_attribute, other, other_attribute):
        raise NotImplementedError("Override this method in child class")

    def __hash__(self):
        raise NotImplementedError("Override this method in child class")

    def __eq__(self, other):
        if hash(self) != hash(other):
            return False
        return self._compare(other) == 0

    def __ne__(self, other):
        if hash(self) != hash(other):
            return True
        return self._compare(other) != 0

    def __lt__(self, other):
        return self._compare(other) == -1

    def __le__(self, other):
        return self._compare(other) != 1

    def __gt__(self, other):
        return self._compare(other) == 1

    def __ge__(self, other):
        return self._compare(other) != -1


class ClassQuery(AbstractQuery, CompareQuery):
    """
    Class to create a query based on object class.
    """

    def __init__(self, class_name):
        super(ClassQuery, self).__init__()
        self.__class_name = class_name.replace('.', '')
        self.__options = {}
        self.uriBase = "/api/class/{0}".format(self.className)

    @property
    def options(self):
        """
        Returns the concatenation of the class and base class options for HTTP
        request query string
        """
        return '&'.join([_f for _f in [AbstractRequest.makeOptions(
            self.__options), super(ClassQuery, self).options] if _f])

    # property setters / getters for this class

    @property
    def className(self):
        """
        Returns the class_name targeted by this ClassQuery
        """
        return self.__class_name

    def _compare(self, other):
        this_url = '{0}/{1}'.format(self.__class_name, self.options)
        other_url = '{0}/{1}'.format(other.className, other.options)
        return (this_url > other_url) - (this_url < other_url)

    def __hash__(self):
        url = '{0}/{1}'.format(self.__class_name, self.options)
        return hash(url)


class DnQuery(AbstractQuery, CompareQuery):
    """
    Class to create a query based on distinguished name (Dn).
    """

    def __init__(self, dn):
        """
        Args:
            dnStr (str): DN to query
        """
        super(DnQuery, self).__init__()
        self.__dn_str = str(dn)
        self.__options = {}
        self.uriBase = "/api/mo/{0}".format(self.__dn_str)

    @property
    def options(self):
        """
        Returns the concatenation of the class and base class options for HTTP
        request query string
        """
        return '&'.join([_f for _f in [AbstractRequest.makeOptions(
            self.__options), super(DnQuery, self).options] if _f])

    # property setters / getters for this class
    @property
    def dnStr(self):
        """
        Returns the base dnString for this DnQuery
        """
        return self.__dn_str

    def _compare(self, other):
        this_url = '{0}/{1}'.format(self.__dn_str, self.options)
        other_url = '{0}/{1}'.format(other.dnStr, other.options)
        return (this_url > other_url) - (this_url < other_url)

    def __hash__(self):
        url = '{0}/{1}'.format(self.__dn_str, self.options)
        return hash(url)


class LoginError(Exception):

    def __init__(self, error_code, reason_str):
        self.error = error_code
        self.reason = reason_str

    def __str__(self):
        return self.reason


def filterUrl(st):
    return st.replace('+', '%2B')


class F5Session(AbstractSession):
    def __init__(self, url, user, password, secure=False, timeout=90,
                 request_format='json'):
        super(F5Session, self).__init__(url, secure, timeout, request_format)
        self._user = user
        self._password = password

    @property
    def user(self):
        """
        Returns the username.
        """
        return self._user

    @property
    def password(self):
        """
        Returns the password.
        """
        return self._password


class SSHSessionException(Exception):
    pass

class SSHSession(paramiko.SSHClient):
    def __init__(self):
        self._ssh = paramiko.SSHClient()
        self._ssh.set_missing_host_key_policy(paramiko.AutoAddPolicy())
        self.max_login_attempts = 2
        self.login_attempts_remaining = 0
        self._resetLoginAttempts()

    def connect(self, *args, **kwargs):
        if self.login_attempts_remaining > 0:
            self.login_attempts_remaining -= 1
            self.close()
            self._ssh.connect(*args, **kwargs)
            self._resetLoginAttempts()
        else:
            message = "SSHSession Exception: " \
                          "Exceeded max number of SSH login attempts (%d)"
            raise SSHSessionException(message%(self.max_login_attempts))

    def exec_command(self, *args, **kwargs):
        return self._ssh.exec_command(*args, **kwargs)

    def _resetLoginAttempts(self):
        self.login_attempts_remaining = self.max_login_attempts

    def close(self):
        self._ssh.close()

    def open_sftp(self):
        return self._ssh.open_sftp()

    def isActive(self):
        return self._ssh.get_transport() and self._ssh.get_transport().is_active()

'''
Function to return the xml
'''


class LoginSession(AbstractSession):

    """
    The LoginSession class creates a login session with a username and password
    """

    def __init__(
            self,
            controller_url,
            user,
            password,
            secure=False,
            timeout=90,
            request_format='xml'):
        """
        Args:
            user (str): Username
            password (str): Password
        """
        super(LoginSession, self).__init__(controller_url, secure, timeout,
                                           request_format)
        self._user = user
        self._password = password
        self._cookie = None
        self._challenge = None
        self._version = None
        self._refresh_time = None
        self._refresh_timeout_seconds = None
        self.user_json=None
        self.login_url=None
        self.logout_url=None
        self.auth=None

    @property
    def user(self):
        """
        Returns the username.
        """
        return self._user

    @property
    def password(self):
        """
        Returns the password.
        """
        return self._password

    @property
    def cookie(self):
        """
        Authentication cookie for this session
        """
        return self._cookie

    @cookie.setter
    def cookie(self, cookie):
        self._cookie = cookie

    @property
    def challenge(self):
        """
        Authentication challenge for this session
        """
        return self._challenge

    @challenge.setter
    def challenge(self, challenge):
        self._challenge = challenge

    @property
    def version(self):
        """
        Returns APIC version received from aaaLogin
        """
        return self._version

    @property
    def refreshTime(self):
        """
        Returns the relative login refresh time. The session must be
        refreshed by this time or it times out
        """
        return self._refresh_time

    @property
    def refreshTimeoutSeconds(self):
        """
        Returns the number of seconds for which this LoginSession is
        valid
        """
        return self._refresh_timeout_seconds

    def getHeaders(self, uri_path_and_options, data):
        headers = {'Cookie': 'APIC-cookie=%s' % self.cookie}
        if self._challenge:
            headers['APIC-challenge'] = self._challenge
        return headers

    def _parseResponse(self, rsp):
        rsp_dict = rsp.json()
        data = rsp_dict.get('imdata', None)
        if not data:
            raise LoginError(0, 'Bad Response: ' + str(rsp.text))

        first_record = data[0]
        if 'error' in first_record:
            error_dict = first_record['error']
            reason_str = error_dict['attributes']['text']
            error_code = error_dict['attributes']['code']
            raise LoginError(error_code, reason_str)
        elif 'aaaLogin' in first_record:
            cookie = first_record['aaaLogin']['attributes']['token']
            refresh_timeout_seconds = first_record['aaaLogin']['attributes']['refreshTimeoutSeconds']
            version = first_record['aaaLogin']['attributes']['version']
            self._cookie = cookie
            self._version = version
            self._refresh_time = int(
                refresh_timeout_seconds) + math.trunc(time.time())
            self._refresh_timeout_seconds = int(refresh_timeout_seconds)
        else:
            raise LoginError(0, 'Bad Response: ' + str(rsp.text))

class DCNMLoginSession(LoginSession):

    """
    The DCNMLoginSession class creates a login session for DCNM with a username and password
    """

    def __init__(
            self,
            controller_url,
            user,
            password,
            secure=False,
            timeout=90,
            request_format='json'):
        """
        Args:
            user (str): Username
            password (str): Password
        """
        super(DCNMLoginSession, self).__init__(
            controller_url, user,password, secure, timeout, request_format)
        self._user = user
        self._password = password
        self._cookie = None
        self._challenge = None
        self._version = None
        self._refresh_time = None
        self._refresh_timeout_seconds = None
        self.user_json = { 'expirationTime': self.timeout * 1000} #in milliseconds
        self.login_url = '/rest/logon'
        self.logout_url = '/rest/logout'
        self.auth=HTTPBasicAuth(self.user, self.password)

    def getHeaders(self, uri_path_and_options, data):
        headers = {
                    'Dcnm-Token': self.cookie,
                    'Content-Type': 'application/json'
                  }
        return headers

    def _parseResponse(self, rsp):
        rsp_dict = rsp.json()
        data = rsp_dict.get('Dcnm-Token', None)
        if not data:
            raise LoginError(0, 'Bad Response: ' + str(rsp.text))
        self._cookie = data
        self._version = 'n/a'
        self._refresh_timeout_seconds = self.timeout
        self._refresh_time = self._refresh_timeout_seconds + math.trunc(time.time())


class NDFCLoginSession(DCNMLoginSession):

    """
    The NDFCLoginSession class creates a login session for DCNM v12 with a username and password
    """

    def __init__(self, *args, **kwargs):
        super(NDFCLoginSession, self).__init__(*args, **kwargs)
        self.login_url = "/login"
        self.user_json.update({
            'userName': self._user,
            'userPasswd': self._password,
            'domain': 'DefaultAuth'
            })
        # self.logout_url = DcnmVersionApiUtils.V12_API + self.logout_url

    def getHeaders(self, uri_path_and_options, data):
        headers = {'Content-Type': 'application/json'}
        if self.cookie:
            headers['Authorization'] = 'Bearer ' + str(self.cookie)
        return headers

    def _parseResponse(self, rsp):
        rsp_dict = rsp.json()
        data = rsp_dict.get('jwttoken', None)
        if not data:
            raise LoginError(0, 'Bad Response: ' + str(rsp.text))
        self._cookie = data
        self._version = 'n/a'
        self._refresh_timeout_seconds = self.timeout
        self._refresh_time = self._refresh_timeout_seconds + math.trunc(time.time())



class MSOLoginSession(LoginSession):
    """
    The MSOLoginSession class creates a login session for MSO with a username and password
    """

    def __init__(
            self,
            controller_url,
            user,
            password,
            secure=False,
            timeout=90,
            request_format='json'):
        """
        Args:
            user (str): Username
            password (str): Password
        """
        super(MSOLoginSession, self).__init__(
            controller_url, user,password, secure, timeout, request_format)
        self._user = user
        self._password = password
        self._cookie = None
        self._challenge = None
        self._version = None
        self._refresh_time = None
        self._refresh_timeout_seconds = None
        self.user_json = {
                        'username': self.user,
                        'password': self.password
                    }
        self.login_url = '/api/v1/auth/login'
        self.logout_url = '/api/v1/auth/logout'
        self.auth=HTTPBasicAuth(self.user, self.password)

    def getHeaders(self, uri_path_and_options, data):
        if self._cookie  == None:
            headers = {
                'Content-Type': 'application/json'
            }
        else:
            bearer = 'Bearer '+self._cookie
            headers = {
                'Authorization': bearer,
                'Content-Type': 'application/json'
            }
        return headers

    def _parseResponse(self, rsp):
        rsp_dict = rsp.json()
        data = rsp_dict.get('token', None)
        if not data:
            raise LoginError(0, 'Bad Response: ' + str(rsp.text))
        self._cookie = data
        self._version = 'n/a'
        self._refresh_timeout_seconds = self.timeout
        self._refresh_time = self._refresh_timeout_seconds + math.trunc(time.time())

class LoginRequest(AbstractRequest):
    """
    LoginRequest for standard user/password based authentication
    """
    def __init__(self, session):
        if session.user_json is None:
            self.user_json = {
                'aaaUser': {
                    'attributes': {
                        'name': session.user,
                        'pwd': session.password
                    }
                }
            }
        else:
            self.user_json = session.user_json
        super(LoginRequest, self).__init__()
        self.user = session.user
        self.password = session.password
        self.timeout = session.timeout

    @property
    def data(self):
        return json.dumps(self.user_json)

    def requestargs(self, session):
        uri_path_and_options = self.getUriPathAndOptions(session)
        headers = session.getHeaders(uri_path_and_options, self.data)
        kwargs = {
            'headers': headers,
            'verify': session.secure,
            'data': self.data,
            'timeout': session.timeout
        }
        return kwargs

    @staticmethod
    def getUrl(session, url=None):
        if session.login_url is None:
            # for apic, for dcnm pass login url
            url = '/api/aaaLogin.json'
        else:
            url = session.login_url
        return session.url + url


class LoginHandler(object):
    @classmethod
    def login(cls, session):
        login_request = LoginRequest(session)
        url = login_request.getUrl(session, session.login_url)
        if session.auth:
            rsp = requests.post(url,
                                auth=session.auth,
                                **login_request.requestargs(session))
        else:
            rsp = requests.post(url, **login_request.requestargs(session))
        session._parseResponse(rsp)

    @classmethod
    def logout(cls, session, accessimpl):
        logout_request = LogoutRequest()
        accessimpl.post(logout_request)

    @classmethod
    def refresh(cls, session, accessimpl):
        refresh_request = RefreshRequest(session.cookie)
        if isinstance(session, DCNMLoginSession):
            cls.login(session)
        elif isinstance(session, NDFCLoginSession):
            cls.login(session)
        elif isinstance(session, MSOLoginSession):
            cls.login(session)
        else:
            session._parseResponse(accessimpl._get(refresh_request))


class LogoutRequest(AbstractRequest):
    """
    Session logout request for standard user/password based authentication
    """

    def __init__(self):
        super(LogoutRequest, self).__init__()

    @staticmethod
    def getUrl(session, url=None):
        if session.logout_url is None:
            # for apic, for dcnm pass login url
            url="/api/aaaLogout.json"
        else:
            url = session.logout_url
        return session.url + url


    def requestargs(self, session):
        uri_path_and_options = self.getUriPathAndOptions(session)
        headers = session.getHeaders(uri_path_and_options, None)
        kwargs = {
            'headers': headers,
            'verify': session.secure,
            'timeout': session.timeout
        }
        return kwargs


class RefreshRequest(AbstractRequest):
    """
    Session refresh request for standard user/password based authentication
    """

    def __init__(self, cookie):
        super(RefreshRequest, self).__init__()
        self.cookie = cookie

    @staticmethod
    def getUrl(session, url=None):
        if url is None:
            # for apic, for dcnm pass login url
            url = '/api/aaaRefresh.json'
        return session.url + url


class RestAccess(object):
    loginHandlers = {
        LoginSession: LoginHandler,
        NDFCLoginSession: LoginHandler,
        DCNMLoginSession: LoginHandler,
        MSOLoginSession: LoginHandler
    }

    def __init__(self, session):
        self._session = session
        self._requests = requests.Session()

    def login(self):
        """
        Authenticate the user/certification provided by the session
        object.
        Args:
            session (LoginSession/CertSession): Session object
        """
        session_class = self._session.__class__
        login_handler = RestAccess.loginHandlers.get(session_class, None)
        if login_handler is not None:
            login_handler.login(self._session)

    def logout(self):
        session_class = self._session.__class__
        login_handler = RestAccess.loginHandlers.get(session_class, None)
        if login_handler is not None:
            login_handler.logout(self._session, self)

    def refreshSession(self):
        """Refresh the _cookie for the given session object
        Args:
            session (LoginSession/CertSession)
        """
        session_class = self._session.__class__
        login_handler = RestAccess.loginHandlers.get(session_class, None)
        if login_handler is not None:
            login_handler.refresh(self._session, self)

    def _get(self, request):
        """
        Internal _get method which performs raw request and returns requests
        response object
        """
        uri_path_and_options = request.getUriPathAndOptions(self._session)
        headers = self._session.getHeaders(uri_path_and_options, None)
        return self._requests.get(
            request.getUrl(
                self._session),
            headers=headers,
            verify=self._session.secure,
            timeout=self._session.timeout)

    def get(self, request):
        """Return data from the server for the given request on the
        given session
        Args:
            request (DnQuery/ClassQuery/TraceQuery/AbstractQuery child): Query
                object
        Return:
            requests.response
        """
        rsp = self._get(request)
        if rsp.status_code != requests.codes.ok:
            return self.__parseError(rsp, QueryError, rsp.status_code)
        return self.__parseResponse(rsp)

    def _response_ok(self, session, response):
        """
        returns True if response is 202 for dcnm or 200 for ACI
        :return: True or False
        """
        if isinstance(session, DCNMLoginSession) and response.status_code in \
            [200, 202]:
            return True
        elif response.status_code == requests.codes.ok:
            return True
        return False

    def post(self, request):
        """Return data from the server for the given request on the
        given session by posting the data in the request object
        Args:
            request (ConfigRequest): ConfigRequest object
        Return:
            requests.response
        """
        url = request.getUrl(self._session)
        rsp = self._requests.post(url, **request.requestargs(self._session))
        if not self._response_ok(self._session, rsp):
            return self.__parseError(rsp, CommitError, rsp.status_code)
        return rsp

    def __parseError(self, rsp, error_class, http_code):
        try:
            if self._session.formatType == AbstractSession.XML_FORMAT:
                parseXMLError(rsp.text, error_class, http_code)
            elif self._session.formatType == AbstractSession.JSON_FORMAT:
                parseJSONError(rsp.text, error_class, http_code)
        except ValueError as ex:
            raise RestError(None, str(ex), http_code)

    def __parseResponse(self, rsp):
        if self._session.formatType == AbstractSession.XML_FORMAT:
            return self.__fromXMLStr(rsp.text)
        return self.__fromJSONStr(rsp.text)

    def __fromXMLStr(self, xml_str):
        xml_root_node = ET.fromstring(xml_str)
        return xml_root_node

    def __fromJSONStr(self, json_str):
        # Remove the children and add it from the fetch data set
        mo_dict = json.loads(json_str)
        return mo_dict

    def __byteify(self, json_input):
        if isinstance(json_input, dict):
            return {self.__byteify(key): self.__byteify(value)
                    for key, value in list(json_input.items())}
        elif isinstance(json_input, list):
            return [self.__byteify(element) for element in json_input]
        elif isinstance(json_input, str):
            return json_input.encode('utf-8')
        else:
            return json_input


def parseJSONError(rsp_text, error_class, http_code=None):
    try:
        rsp_dict = json.loads(rsp_text)
        data = rsp_dict.get('imdata', None)
        if data:
            first_record = data[0]
            if 'error' == list(first_record.keys())[0]:
                error_dict = first_record['error']
                reason_str = error_dict['attributes']['text']
                error_code = error_dict['attributes']['code']

                if error_class:
                    raise error_class(error_code, reason_str, http_code)
                raise ValueError(reason_str)
    except BaseException:
        raise ValueError(rsp_text)


def parseXMLError(rsp_str, error_class, http_code=None):
    error_node = ET.fromstring(rsp_str).find('error')
    if error_node is not None:
        error_str = error_node.attrib['text']
        error_code = error_node.attrib['code']
        raise error_class(int(error_code), error_str, http_code)
    raise ValueError(rsp_str)


class RestError(Exception):
    def __init__(self, error_code, reason_str, http_code):
        self.reason = reason_str
        self.error = error_code
        self.http_code = http_code

    def __str__(self):
        return self.reason


class CommitError(RestError):
    def __init__(self, error_code, reason_str, http_code=None):
        super(CommitError, self).__init__(error_code, reason_str, http_code)


class QueryError(RestError):
    def __init__(self, error_code, reason_str, http_code=None):
        super(QueryError, self).__init__(error_code, reason_str, http_code)


class F5RestAccess(object):
    def __init__(self, session):
        """
        Arguments:
            session: Specifies a session
        """
        self._session = session

    def reauth(self):
        pass

    def logout(self):
        pass

    def getRawResponseWithPaging(self, url):
        pass

    def getRawResponse(self, url):
        rsp = self.getRawResponseObject(url)
        return rsp.status_code, rsp.text

    def getRawResponseObject(self, url):
        rsp = requests.get(url, headers=None,
                           auth=(self._session.user, self._session.password),
                           verify=self._session.secure,
                           timeout=self._session.timeout)
        return rsp

class DirectRestAccess(object):
    """
    The RestAccessInitclass creates a connection to the APIC and the MIT.
    It requires an existing session and endpoint.
    """

    def __init__(self, session):
        """
        Arguments:
            session: Specifies a session
        """
        self._access_impl = RestAccess(session)
        self.session = session

    def login(self):
        """
        Creates a session to an APIC.
        """
        self._access_impl.login()

    def logout(self):
        """
        Ends a session to an APIC.
        """
        self._access_impl.logout()

    def reauthOrLogin(self, logger=None):
        """
        This is needed to handle reauth failure in case session is expired
        """
        try:
            self.reauth()
        except Exception as e:
            if logger:
                logger.warning("Reauth failed with exception: " + str(e) +
                             " trying login instead.")
            self.login()

    def reauth(self):
        """
        Re-authenticate this session with the current authentication cookie.
        This method can be used to extend the validity of a successful login
        credentials. This method may fail if the current session expired on
        the server side. If this method fails, the user must login again to
        authenticate and effectively create a new session.
        """
        self._access_impl.refreshSession()

    def query(self, query_object):
        """
        Queries the MIT for a specified object. The query_object provides a
        variety of search options.
        """
        return self._access_impl.get(query_object)

    def lookupByDn(self, dn_str_or_dn, **query_params):
        """
        A short-form managed object (MO) query using the distinguished name(Dn)
        of the MO.

        Args:
          dn_str_or_dn:   dn of the object to lookup
          query_params: a dictionary including the properties to the
            added to the query.
        """
        dn_query = DnQuery(dn_str_or_dn)
        self.__setQueryParams(dn_query, query_params)
        mos = self.query(dn_query)
        return mos if mos else None

    def lookupByClass(self, class_names, parent_dn=None, **query_params):
        """
        A short-form managed object (MO) query by class.

        Args:
          class_names: Name of the class to lookup
          parent_dn:   dn of the root object were to start search from (optional)
          query_params: a dictionary including the properties to the
            added to the query.
        """
        if parent_dn:
            dn_query = DnQuery(parent_dn)
            dn_query.classFilter = class_names
            dn_query.queryTarget = 'subtree'
            self.__setQueryParams(dn_query, query_params)
            mos = self.query(dn_query)
        else:
            class_query = ClassQuery(class_names)
            self.__setQueryParams(class_query, query_params)
            mos = self.query(class_query)
        return mos

    @staticmethod
    def __setQueryParams(query, query_params):
        """Utility function to set the query parameters.

        Utility function used to set in the 'query' passed as
        argument, the 'query_params' dictionary. The key in the
        dictionary will be used as the property name to set, with
        the value content.

        Args:
          query: query class to be modified
          query_params: a dictionary including the properties to the
            added to the query.
        """
        for param, value in list(query_params.items()):
            if value is not None:
                setattr(query, param, value)

    def getRawResponseObject(self, apic_url):
        headers = self.session.getHeaders(apic_url, None)
        rsp = requests.get(apic_url, headers=headers, verify=self.session.secure, timeout=self.session.timeout)
        return rsp

    def getRawResponse(self, apic_url):
        headers = self.session.getHeaders(apic_url, None)
        rsp = requests.get(apic_url, headers=headers,
                           verify=self.session.secure,
                           timeout=self.session.timeout)
        return rsp.status_code, rsp.text

    def post(self, apic_url, data):
        headers = self.session.getHeaders(apic_url, None)
        rsp = requests.post(
            apic_url,
            headers=headers,
            data=data,
            verify=self.session.secure,
            timeout=self.session.timeout)
        rsp_status_code, rsp_text = (rsp.status_code, rsp.text.encode('utf-8'))
        return rsp_status_code, rsp_text

    def setPageParams(self, url, page_num, page_size):
        if '?' in url:
            url = url + '&page=' + str(page_num) + \
                '&page-size=' + str(page_size)
        else:
            url = url + '?page=' + str(page_num) + \
                '&page-size=' + str(page_size)
        return url

    def getRawResponseWithPaging(self, base_url, url):
        page_size = int(self.getPageSize(base_url))
        page_num = 0
        merged_json = None
        while (True):
            newurl = self.setPageParams(url, page_num, page_size)
            rsp_status_code, rsp_text = self.getRawResponse(newurl)
            if rsp_status_code != requests.codes.ok:
                rsp_text = "paging query pg.%d failed with response: %s"%(
                    page_num, rsp_text)
                return (rsp_status_code, rsp_text)
            else:
                json_doc = json.loads(rsp_text)
                total_objects = len(json_doc['imdata'])
                if merged_json is None:
                    merged_json = json_doc
                else:
                    merged_json['imdata'] = json_doc['imdata'] + \
                        merged_json['imdata']
                if total_objects < page_size:
                    break
                else:
                    page_num = page_num + 1

        rsp_status_code = rsp_status_code
        rsp_text = json.dumps(merged_json)

        return (rsp_status_code, rsp_text)

    def getPageSize(self, apic_url):
        page_query = '/api/class/commSetup.json'
        url = apic_url + page_query
        rsp_status_code, rsp_text = self.getRawResponse(url)
        if rsp_status_code == requests.codes.ok:
            json_doc = json.loads(rsp_text)
            page_size = json_doc['imdata'][0]['commSetup']['attributes']['maxMos']
        else:
            # default page size of APIC
            page_size = 100000

        return page_size


def parseFilterNodeIds(node_ids):
    if not node_ids:
        return []
    return [int(x) for x in node_ids if x.isdigit()]

def parseQueryIds(query_ids):
    if not query_ids:
        return []
    (valid, failing) = ([], [])
    for query_id in query_ids.split(','):
        try:
            valid.append(getattr(QueryId, query_id))
        except AttributeError as e:
            failing.append(query_id)
    if len(failing) > 0:
        raise CandidDataCollectionException(
            'Invalid query_ids: ' + ','.join(failing))

    return valid


def candidCheckModuleVersion(logger, third_party_svc_ctx):
    version_check = True
    if setuptools.__version__ != "34.3.3":
        version_check = True
        logger.warning(
            "Please install setuptools version 34.3.3, refer to README.md")
    if requests.__version__ != "2.10.0":
        version_check = False
        logger.warning(
            "Please install requests version 2.10.0, refer to README.md")
    if paramiko.__version__ != "2.0.1":
        version_check = False
        logger.warning(
            "Please install paramiko version 2.0.1, refer to README.md")
    if not ThirdPartyServicesAPI.checkModuleVersions(
            logger, third_party_svc_ctx):
        version_check = False
    return True

class StandaloneTopologyArgs(object):

    accepted_node_types = [STANDALONE_SPINE, STANDALONE_LEAF, DCNM]
    accepted_headers = ["node_type", "user", "node_ip_or_node_name"]

    class NodeInfo(object):
        def __init__(self, node_type, user, node_ip_or_node_name):
            self.node_type = node_type
            self.user = user
            self.node_ip_or_node_name = node_ip_or_node_name

    def __init__(self, sa_fabric, user=None, dcnms=[]):
        self.node_info_list = []
        self.sa_fabric = sa_fabric
        self.user = user
        self.dcnms = dcnms

    def parseStandaloneInputTopology(self, standalone_input):
        self._parseStandaloneInput(standalone_input)

    def addStandaloneLeafs(self, standalone_leafs):
        self._parseStandaloneNodes(
            STANDALONE_LEAF, self.user, standalone_leafs)

    def addStandaloneSpines(self, standalone_spines):
        self._parseStandaloneNodes(
            STANDALONE_SPINE, self.user, standalone_spines)

    def addDcnms(self, dcnms):
        if not dcnms:
            return
        for dcnm in dcnms:
            self._parseStandaloneNodes(
                DCNM, self.user, dcnm)

    def _parseStandaloneInput(self, csvfile):
        if not csvfile:
            return
        with open(csvfile) as f:
            readCSV = csv.DictReader(f)
            res, msg = self._validateHeaders(readCSV)
            assert res, msg
            for row_dict in readCSV:
                if not row_dict:
                    continue
                res, msg = self._validateCsvRow(row_dict)
                assert res, "\n error parsing {} \n at line number {} \n {} " \
                            "".format(row_dict, readCSV.line_num, msg)
                self.node_info_list.append(
                    StandaloneTopologyArgs.NodeInfo(
                        node_type=row_dict["node_type"],
                        user=row_dict["user"],
                        node_ip_or_node_name=row_dict["node_ip_or_node_name"]))

    def _parseStandaloneNodes(self, node_type, user, node_ips_or_node_names):
        if not node_ips_or_node_names:
            return
        if not isinstance(node_ips_or_node_names, list):
            node_ips_or_node_names = [node_ips_or_node_names]
        for node in node_ips_or_node_names:
            self.node_info_list.append(
                StandaloneTopologyArgs.NodeInfo(
                    node_type=node_type,
                    user=user,
                    node_ip_or_node_name=node))

    def _validateHeaders(self, csvfile):
        headers = csvfile.fieldnames
        if not headers:
            return False, "Empty headers found. Accepted Headers " \
                          "of csv {}".format(self.accepted_headers)

        if len(headers) != 3 or \
            (any(header not in self.accepted_headers for header in headers)):
            return False, "Invalid headers found. Accepted Headers " \
                          "of csv {}".format(self.accepted_headers)
        return True, ""

    def _validateCsvRow(self, entry):
        msg = []
        res = True
        if entry["node_type"] not in self.accepted_node_types:
            res = False
            msg.append("{} node type is invalid".format(entry["node_type"]))
            msg.append("Acceped node types are {}".format(
                self.accepted_node_types))
        if entry["user"] == "" :
            res = False
            msg.append("User can't be empty")
        if entry["node_ip_or_node_name"] == "":
            res = False
            msg.append("node_ip_or_node_name can't be empty")
        return res, msg

class ArgumentsValidator(object):

    def getExtraAndMissingArgs(self, args_dict, accepted_args, required_args,
                               extra_args, missing_args):
        for k,v in list(args_dict.items()):
            if k in required_args and v is None:
                missing_args.append(k)
            elif k not in accepted_args and v is not None:
                extra_args.append(k)

    def validateStandaloneArgs(self, args_dict):
        assert (args_dict["cnaeMode"] == _STANDALONE)
        res = True
        msg = []
        usage = \
        ["Standalone Usage (Required args): ",
         "-DCNM, -user, -clusterName, -lanUsername -leafCredentialOverwrite or",
         "-standaloneInput, -clusterName or",
         "-user, -clusterName, -standaloneLeafs, -standaloneSpines, -lanUsername -leafCredentialOverwrite"]

        if args_dict["standaloneInput"] is not None:
            if not os.path.exists(args_dict["standaloneInput"]):
                res = False
                msg.append(
                    "File not found at {}".format(args_dict["standaloneInput"]))

        if args_dict["DCNM"] is not None or \
                args_dict["standaloneSpines"] is not None or \
                args_dict["standaloneLeafs"] is not None:
            if args_dict["user"] is None:
                res = False
                msg.append("-user Required")
            if args_dict["lanUsername"] is None:
                res = False
                msg.append("-lanUsername Required")

        if args_dict["DCNM"] is None and \
                args_dict["standaloneSpines"] is None and \
                args_dict["standaloneLeafs"] is None and \
                args_dict["standaloneInput"] is None:
            res = False

        if "inband" in [args_dict.get("connectionPreferencePrimary"),
                        args_dict.get("connectionPreferenceSecondary")] and \
                args_dict.get("loopbackInterface") < 0:
            res = False
            msg.append("-loopbackInterface must be >= 0 when primary or secondary connection preference is inband")

        if not res:
            msg.extend(usage)
        return res, msg

    def validateApicArgs(self, args_dict):
        assert (args_dict["cnaeMode"] == _APIC)
        res = True
        msg = []
        if args_dict[_APIC] is None:
            res = False
            msg.append("-APIC required")
        if args_dict["clusterName"] is None:
            res = False
            msg.append("-clusterName required")
        if args_dict["user"] is None:
            res = False
            msg.append("-user required")
        return res, msg

    def validateMsoArgs(self, args_dict):
        assert (args_dict["cnaeMode"] == _MSO)
        res = True
        msg = []
        if args_dict[_MSO] is None:
            res = False
            msg.append("-MSO required")
        if args_dict["user"] is None:
            res = False
            msg.append("-user required")
        return res, msg

def addStandaloneArguments(parser):
    parser.add_argument(
        '-standaloneInput',
        required=False,
        help='Used for NX FABRIC, Specify path to csv file if the '
             'script should read topo info from the file instead. '
             'Headers of csv - node_type, user and node_ip_or_node_name')
    parser.add_argument(
        "-standaloneLeafs",
        nargs='+',
        required=False,
        help='Specify names/ips of all the leafs in the NX FABRIC')
    parser.add_argument(
        "-standaloneSpines",
        nargs='+',
        required=False,
        help="Specify names/ips of all the spines in the NX FABRIC")
    parser.add_argument(
        '-DCNM',
        action="store",
        nargs='+',
        help='Specify DCNM IPs or Names separated by space. ' +
        'Example, python cnae_data_collection cnaeMode STANDALONE -DCNM '
        'dcnm_ip1 dcnm_ip2',
        required=False)
    parser.add_argument(
        "-siteName",
        required=True,
        help="Specify the name of NX FABRIC to be assured")
    parser.add_argument(
        '-dcnmVersion',
        help="DCNM software version",
        dest='dcnmVersion',
        default=",".join(SUPPORTED_DCNM_VERSIONS),
        required=False)
    parser.add_argument(
        '-lanUsername',
        required=False,
        default=None,
        help="Specify the default LAN credentials for the NX FABRIC")
    parser.add_argument(
        '-leafCredentialOverwrite',
        type=int,
        required=False,
        dest='leafCredentialOverwrite',
        default=0,
        help="Specify if there is any leaf switch that needs login credentials other than default Lan credentials")
    parser.add_argument(
        '-loopbackInterface',
        type=int,
        required=False,
        default=-1,
        help="Specify loopback number to retrieve inband ips from DCNM")

def addMsoArguments(parser):
    parser.add_argument(
        '-MSO',
        action="store",
        nargs='+',
        help='Specify MSO IPs or Name separated by space. ' +
             'Example, python cnae_data_collection -MSO mso_ip1 mso_ip2',
        required=True)
    #TODO: add additional params - mso version

def addApicArguments(parser):
    parser.add_argument(
        '-APIC',
        action="store",
        nargs='+',
        help='Specify APIC Controller IPs or Name separated by space. ' +
        'Example, python cnae_data_collection -APIC apic_ip1 apic_ip2',
        required=True)
    parser.add_argument(
        '-aciVersion',
        help="ACI software version",
        dest='aciVersion',
        default=",".join(SUPPORTED_ACI_VERSIONS),
        required=False)
    parser.add_argument('-apicLoginTimeOut', type=int, help=argparse.SUPPRESS,
                        dest='apicLoginTimeOut', default=6, required=False)
    parser.add_argument('-apicQueryTimeOut', type=int, help=argparse.SUPPRESS,
                        dest='apicQueryTimeOut', default=60, required=False)
    parser.add_argument('-apicNodeTimeOut', type=int, help=argparse.SUPPRESS,
                        dest='apicNodeTimeOut', default=600, required=False)
    parser.add_argument('-apicConfigExportPolicyName', type=str,
                        default=None, required=False,
                        dest='apicConfigExportPolicyName',
                        help="Specify apic config export policy name")
    parser.add_argument('-apicConfigExportFormat', type=str,
                        default="xml", required=False,
                        dest='apicConfigExportFormat', choices=['xml', 'json'],
                        help="Specify apic config export policy format")
    parser.add_argument('-apicConfigExportTimeOut', type=int,
                        default=600, required=False,
                        dest='apicConfigExportTimeOut',
                        help="Specify apic config export policy timeout ")

def addCommonArguments(parser):
    parser.add_argument(
        '-cnaeMode',
        type=str,
        required=False,
        dest='cnaeMode',
        choices=[
            'APIC',
            'STANDALONE',
            'MSO'],
        default='APIC',
        help="Specify network topology deployment mode (APIC, Standalone, MSO)")
    parser.add_argument(
        "-clusterName",
        required=True,
        help="Specify a name for APIC/DCNM/MSO Fabric")
    parser.add_argument(
        "-user",
        required=False,
        help="Specify user name to login to fabric")
    parser.add_argument(
        '-targetDir', action="store",
        help="Specify destination directory to dump data",
        dest='targetDir',
        default="./",
        required=False)
    parser.add_argument('-maxThreads', type=int,
                        help="Specify maximum number of threads for polling",
                        dest='maxThreads', default=16,
                        required=False)
    parser.add_argument('-iterations', type=int, help=argparse.SUPPRESS,
                        dest='iterations', default=3, required=False)
    parser.add_argument(
        '-iterationIntervalSec',
        type=int,
        help=argparse.SUPPRESS,
        dest='iterationIntervalSec',
        default=180,
        required=False)
    parser.add_argument('-queryIds', help=argparse.SUPPRESS,
                        dest='queryIds', default='', required=False)
    parser.add_argument(
        '-switchVersion',
        help="Switch software version",
        dest='switchVersion',
        required=False)
    parser.add_argument(
        '-optimizedQuery',
        help=argparse.SUPPRESS,
        dest='optimizedQuery',
        action='store_true',
        required=False)
    parser.add_argument(
        '-noLegacyQuery',
        help=argparse.SUPPRESS,
        dest='noLegacyQuery',
        action='store_true',
        required=False)
    parser.add_argument(
        '-filterNodeIds',
        default='',
        action="store",
        nargs='+',
        help=argparse.SUPPRESS,
        required=False)
    parser.add_argument('-loginTimeOut', type=int, help=argparse.SUPPRESS,
                        dest='loginTimeOut', default=6, required=False)
    parser.add_argument('-queryTimeOut', type=int, help=argparse.SUPPRESS,
                        dest='queryTimeOut', default=60, required=False)
    parser.add_argument('-nodeTimeOut', type=int, help=argparse.SUPPRESS,
                        dest='nodeTimeOut', default=1200, required=False)
    parser.add_argument(
        '-thirdPartyServices',
        help='Third-party services configuration file',
        required=False)
    parser.add_argument('-versionProperties', type=str, required=False,
                        help='Specify path to version.properties file',
                        default='version.properties')
    parser.add_argument(
        '-connectionPreferencePrimary',
        type=str,
        default="inband",
        required=False,
        dest='connectionPreferencePrimary',
        choices=[
            'outofband',
            'inband'],
        help="Specify primary connection preference for data collection")
    parser.add_argument(
        '-connectionPreferenceSecondary',
        type=str,
        default="outofband",
        required=False,
        dest='connectionPreferenceSecondary',
        choices=[
            'outofband',
            'inband'],
        help="Specify secondary connection preference for data collection")
    parser.add_argument(
        '-nat',
        required=False,
        default=None,
        help="specify a nat configuration json file")

def runCandidDataCollectionOffline():
    """
    runCandidDataCollectionOffline is called in Offline mode only.
    Arguments can be passed to run in :
    1) APIC mode - collects data from APIC
    2) standalone mode - gets topo info from csv or from cli
     and collect data from standalone switches
    3) MSO mode - collects data from MSO
    """
    validate_arguments = ArgumentsValidator()
    parser = argparse.ArgumentParser(
        description="script to poll data from APIC/DCNM/LEAFS/MSO")

    addCommonArguments(parser)
    partial_args, _ = parser.parse_known_args()
    if partial_args.cnaeMode == _STANDALONE:
        addStandaloneArguments(parser)
    elif partial_args.cnaeMode == _MSO:
        addMsoArguments(parser)
    else:
        addApicArguments(parser)

    args = parser.parse_args()

    if args.cnaeMode == _APIC:
        args.__dict__["entityIps"] = args.__dict__[_APIC]
        args.__dict__["filterNodeIds"] = parseFilterNodeIds(args.filterNodeIds)
        res, msg = validate_arguments.validateApicArgs(args.__dict__)
    elif args.cnaeMode == _STANDALONE:
        args.__dict__["entityIps"] = args.__dict__['DCNM']
        res, msg = validate_arguments.validateStandaloneArgs(args.__dict__)
    elif args.cnaeMode == _MSO:
        args.__dict__["entityIps"] = args.__dict__['MSO']
        res, msg = validate_arguments.validateMsoArgs(args.__dict__)
    else:
        assert False, "cnaeMode couldnt be determined - APIC or STANDALONE or MSO"
    if not res:
        for m in msg:
            print(m)
        sys.exit(1)
    args.queryIds = parseQueryIds(args.queryIds)

    try:
        config = ThirdPartyServicesAPI.readServiceConfig(
            args.__dict__['thirdPartyServices'])
        svc_ctx = ThirdPartyServicesAPI.initialize(config)
        args.__dict__['thirdPartyServiceContext'] = svc_ctx
    except Exception as e:
        raise SystemExit(str(e))
    candidDataCollectionOffline(args)

class FeatureManager():
    @staticmethod
    def isQueryApplicable(logger, node = None, query = None):
        if node.node_role in ['standalone_leaf', 'standalone_spine'] :
            logger.debug("checking for query applicability")
            logger.debug("node enabled features = %s" %(node.enabled_features))

            query_features_req = query.getFeatureSet()
            logger.debug("query features = %s" %(query_features_req))

            if not node.enabled_features:
                logger.debug("no node features enabled, query applicable for backward compatibility")
                return True

            if not query_features_req:
                logger.debug("no query features needed, query applicable")
                return True

            for feature in query_features_req:
                logger.debug("check applicability for query feature %s" %(feature))
                if feature not in node.enabled_features:
                    logger.debug("feature not enabled for node, query not applicable")
                    return False

            return True
        else:
            return True

if __name__ == "__main__":
    runCandidDataCollectionOffline()
