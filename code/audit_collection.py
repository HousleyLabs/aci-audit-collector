"""
Comments:
Developed by Housley Communications - Tony Condran
Dec 2020
Vs 0.2

This is ShareMeWare:
Yours to use but we would appreciate Housley name and URL in comments section
https:// www.housley.com.au

 :-)

Run Notes
- Code written for Linux as directory seperators are /
- Infact best run from docker container - code provided
"""


from pprint import pprint, pformat
import os, getpass, logging

from lib import tools, session



def main(args):
    # Make instance of tools
    tls = tools.tools()

    # Set logging Level
    if args.debug:
        logging.basicConfig(level=logging.DEBUG)
        print("Debug Mode")

    else:
       logging.basicConfig(level=logging.INFO, format='%(message)s')

    # Banner
    os.system("clear")
    tls.colour_output(text="*"*80, fg="YELLOW",bg="BLUE")
    tls.colour_output(text="*********************** Housley ACI Audit:Data Collector ***********************", fg="YELLOW",bg="BLUE")
    tls.colour_output(text="*"*80, fg="YELLOW",bg="BLUE")

    logging.debug(pformat(args))


    # Read audit file
    logging.info("Reading audit list from file: " + args.json)
    audit_list = tls.read_JSON(args.json)

    # Setup output folder/directory
    # The zipped file name will also be the same as the folder
    if args.output != None:
        tar_file = args.output
        new_dir = "../" + args.output
        logging.debug("Creating output directory: " + new_dir)

        # Make Dir and confirm sucessful
        if tls.make_dir(dir_name=new_dir):
            out_dir = new_dir + "/"

        # Directory creation failed
        else:
            exit()

    else:
        tar_file = "output"
        out_dir = "../output/"


    logging.info("Output directory used: " + out_dir + "\n")

    # Check if testing mode
    if args.testing:
    # Set variables
        ip_addr = "172.16.11.2"
        user = "T18"
        #passwd = "PROMPT"
        passwd = "!@34QWer"

    # Get variable if not testing
    else:
        # Set password for prompted input
        passwd = "PROMPT"

        # Enter Login Credentials if Prompt is True
        if args.prompted:
            # Get APIC IP address
            vPrompt = str("Input IP address for APIC: ")
            ip_addr = input(vPrompt)
            if not tls.validate_ip(ip_addr):
                logging.info("Input cancelled")
                exit()

            # Get Username
            vPrompt = str("Input APIC login username: ")
            user = input(vPrompt)


        # If not prompted - assumes user and apic ar provided
        else:
            if args.user == None or args.apic == None:
                logging.info("Run error ... Username and APIC details not provided")
                logging.info("run again with either:")
                logging.info("-a and -u options")
                logging.info(" or ")
                logging.info("-p prompt option ")
                exit()

            else:
                user = args.user
                ip_addr = args.apic


    # Get password
    if passwd == "PROMPT":
        vPrompt = str("Input Password for " + user + " at APIC " + ip_addr + ": ")
        password = getpass.getpass(vPrompt)

    else:
        password = passwd



    # Try to login to APCI
    logging.info("Checking APIC connection is possible")
    try:
        aci = session.Session(apic=ip_addr, https=True, uid=user, pwd=password, verify_ssl=False)
        login_successful = aci.login()

    except:
        logging.info("\nError - Login failed - Not able to connect")
        exit()

    # Check if login ok
    if login_successful:
        logging.debug("  Session token: " + str(aci.session.cookies))
        logging.info("  Login sucessful")

    else:
        logging.info("\nError - Login failed - Check Password for user: " + user + "\n")
        exit()



    # Parse the json list of objects to collect
    logging.info("\n\n##### Auditing System #####")
    for line in audit_list["audit_list"]:
        if line.get("url") != None:  # Check not section seperator
            obj = line["url"]
            logging.info("\nGetting name: " + line["name"])
            logging.debug(obj)

            if line["include"] == True:
                resp = aci.get(obj)
                tls.write_JSON(name=line["name"], content=resp, dir_name=out_dir)
                logging.debug(resp)

            else:
                 logging.info("  Skipped as included=False in audit.json config file")


    # Make the tar.gz file
    tls.make_tar_file(name=tar_file)
    logging.info("\n\nAudit files archived to: " + tar_file + ".tar.gz")


    logging.info("\n\n##### Audit Complete #####")
    logging.info("Please send " + tar_file + ".tar.gz to Housley\n\n")



if __name__ == '__main__':
    print("\n!!!\n!!! You need to run the code via run.py not directly\n!!!")
