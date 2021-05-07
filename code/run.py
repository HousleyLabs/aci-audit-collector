"""
Comments:
Developed by Housley Communications - Tony Condran
Dec 2020
Vs 0.2

This is ShareMeWare:
Yours to use but we would appreciate Housley name and URL in comments section
https:// www.housley.com.au

 :-)

Inital run parameters to capture input and provide run options

"""

from pprint import pprint
import argparse

import audit_collection

### Version of Code ###
version = "0.2"


### ArgumentParser ###
parser = argparse.ArgumentParser(description="Housley ACI Audit Script - Version: " + version)

parser.add_argument("-v","--version",
                    action="store_true",
                    help="See version of code")

parser.add_argument("-a","--apic",
                    help="Hostname or IP of APIC")

parser.add_argument("-u","--user",
                    help="Username for login to APIC")

parser.add_argument("-p", "--prompted",
                    action="store_true",
                    help="Prompt for APIC and User during the Audit")

parser.add_argument("-j","--json",
                    default="audit.json",
                    help="Alternative JSON file - other than default of ./audit.json, \
                     this file has the Definition of objects and classes to retrieve from APIC")

parser.add_argument("-o","--output",
                    help="Alternative output folder - other than default of ./output/")

parser.add_argument("-d","--debug",
                    action="store_true",
                    help="debug mode")

parser.add_argument("-t", "--testing",
                    action="store_true",
                    help="Use values embedded in code")

args = parser.parse_args()
# pprint(args)


### Print Version of code ###
if args.version:
    print("Housley Audit Version:\n" + version + "\n")
    exit()


### Check input has minimal arguments ###
if args.testing == False and args.prompted == False:
    if args.user == None or args.apic == None:
        print("Input Error --- APIC and USER need to be specified")
        print("Run with -h argument to see input options")
        exit()


### Run the Audit code ###
audit_collection.main(args)
