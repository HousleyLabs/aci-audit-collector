""" session"""
from pprint import pprint
import requests, urllib3, logging, json

class Session(object):
    def __init__(self, apic=None, https=True, uid=None, pwd=None, verify_ssl=False):
        urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
        self.apic = apic
        self.uid = uid
        self.pwd = pwd
        if https:
            self.api = 'https://%s:443' % self.apic
        else:
            self.api = 'http://%s' % self.apic
        self.session = None
        self.verify_ssl = verify_ssl
        self.obj="/api/mo/uni.json"



    def login(self):
        """
        Login into APIC
        """
        logging.debug('Connecting to the APIC')
        login_obj = self.api + '/api/aaaLogin.json'
        name_pwd = {'aaaUser': {'attributes': {'name': self.uid, 'pwd': self.pwd}}}
        vCred = json.dumps(name_pwd)

        logging.debug("Credentials" + str(vCred))

        self.session = requests.Session()
        ret = self.session.post(login_obj, data=vCred, verify=self.verify_ssl, timeout=15)
        status=self.check_ret(ret)
        return(status)



    def check_ret(self, ret=None):
        """
        Check if return is valid or response error
        """
        logging.debug(ret.text)

        if ret.status_code == 200:
            status = True

        else:
            logging.info("Login failed: status returned: " + str(ret.status_code))
            logging.info("  Reason: " + ret.reason)

            status=False

        return(status)



    def push_to_apic(self, data=None):
        """
        Push the data to the APIC
        """
        post_obj = self.api + self.obj
        logging.debug('Posting obj: %s data: %s', post_obj, data)
        resp = self.session.post(post_obj, data=json.dumps(data))
        logging.debug('Response: %s %s', resp, resp.text)
        logging.info(resp.text)
        return(resp)



    def get(self,obj=None):
        """
        Perform a REST GET call to the APIC
        """

        if obj==None:
            obj=self.obj
            logging.info("no obj")

        else:
            #obj = "/api/mo/" + obj + ".json"
            #obj = "/api/mo/" + obj
            #obj = "/"+obj + ".json"
            logging.info("  obj: " + obj)

        get_obj=self.api + obj
        logging.info("  obj to APIC: " + get_obj)

        logging.debug(get_obj)
        resp = self.session.get(get_obj)
        logging.debug(resp)
        dict=json.loads(resp.text)
        return(dict)
