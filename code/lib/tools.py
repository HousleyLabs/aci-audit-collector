""" tools"""
import os
import string
import re
import sys
from pprint import pprint, pformat
import logging
import json
import tarfile
from colorama import init, Fore, Back, Style
from termcolor import colored

class tools():
    def read_JSON(self,filename):
        """
        Read from file - as JSON/DICT
        Return content of file
        """
        ### Try to Open File ###
        logging.debug("\n******* File Name: " + filename)
        try:
            file = open(filename)
        except:
            logging.info("Could open JSON file: " + filename)
            exit()

        ### Try to Read file ###
        jsondata = file.read()

        try:
            dict = json.loads(jsondata)
        except:
            logging.info("Error importing JSON file data: " + filename)
            logging.info("Format error")
            exit()

        file.close()

        # Lot of output
        logging.debug("\n**** File Dump: ")
        logging.debug(pformat(dict))

        return(dict)



    def write_JSON(self, name="empty", dir_name="./output/", content=""):
        """
        Write to JSON file
        No Return
        """
        filename = dir_name + name + ".json"
        with open(filename, 'w') as outfile:
            json.dump(content, outfile)
            # will auto clase file



    def validate_ip(self, ip_addr=""):
        """
        Validate an IP addess using regular expression
        Return True if is a valid IP Address
        """
        regex = '''^(25[0-5]|2[0-4][0-9]|[0-1]?[0-9][0-9]?)\.(
                    25[0-5]|2[0-4][0-9]|[0-1]?[0-9][0-9]?)\.(
                    25[0-5]|2[0-4][0-9]|[0-1]?[0-9][0-9]?)\.(
                    25[0-5]|2[0-4][0-9]|[0-1]?[0-9][0-9]?)$'''


        # And the string in search() method
        if(re.search(regex, ip_addr)):
            valid_ip = True
        else:
            logging.info("Invalid IP Address")
            valid_ip = False

        return(valid_ip)



    def check_dir_exists(self, dir_name=None):
        """
        Check if a directory already exists
        Return True if already exists
        """
        logging.info("Checking for Output Directory: " + dir_name)

        if os.path.isdir(dir_name):
            logging.info("Output Directory already exists")
            dir_exist = True
        else:
            dir_exist = False

        return(dir_exist)



    def check_dir_empty(self, dir_name=None):
        """
        Check if directory is Empty
        Return True if empty
        """
        if self.get_file_list(dir_name)["files_exist"]:
            msg = "Directory not empty \n \
            Please choose new name or delete existing files or directory"
            # logging.info("Directory is not empty")
            self.colour_output(text=msg, fg="RED",bg="WHITE")
            usable = False

        else:
            usable = True

            # Future feature
            # prompt to confirm deletion and recreation of dir/files
            # issue with deleting - did not add as may delect invalid path and delete wrong stuff
            # need to add later with error checking

        return(usable)



    def make_dir(self, dir_name=None):
        """
        Make a Directory if it doesnt exist
        Return True if successful
        """
        # Check dir exist
        if  self.check_dir_exists(dir_name=dir_name):
            if self.check_dir_empty(dir_name=dir_name):
                logging.info("Output Directory is empty and will be reused")
                dir_made = True

        else:
            logging.debug("Dir does not exist")

            # Create directory
            try:
                os.mkdir(dir_name)
                dir_made = True

            except:
                msg = "Directory creation Failed"
                self.colour_output(text=msg, fg="RED",bg="WHITE")
                dir_made = False

            return(dir_made)



    def colour_input(self, prompt="No Prompt", fg="WHITE", bg="RED", st="RESET_ALL"):
        init()
        responce = input(getattr(Fore,fg) + getattr(Back,bg) + prompt + getattr(Style,st))
        return(responce)



    def colour_output(self, text="No Text given", fg="WHITE", bg="RED", st="RESET_ALL"):
        init()
        # print(getattr(Fore,fg) + getattr(Back,bg)+ text + getattr(Style,st))
        logging.info((getattr(Fore,fg) + getattr(Back,bg) + text + getattr(Style,st)))



    def get_file_list(self,dir_name):
        """
        Get List of files in a directory
        """
        logging.debug("listing file in dir: " + dir_name)

        ret_val = {}
        ret_val["fileList"] = os.listdir(dir_name)

        no_of_files = len(ret_val["fileList"])

        # Check dir has more than 0 files - ie is not empty
        if not no_of_files > 0 :
            logging.debug("No file is in Dir")
            ret_val["files_exist"] = False

        else:
            logging.debug("Number of files: " + str(no_of_files))
            logging.debug("Directory contains following files:")
            logging.debug(pformat(ret_val["fileList"]))
            ret_val["files_exist"] = True

        return(ret_val)



    def make_tar_file(self, name):
        """
        Archive the content a directory to a tar.gz file
        No Return
        """
        source_dir = "../" + name
        output_filename = "../" + name + ".tar.gz"

        with tarfile.open(output_filename, "w:gz") as tar:
            tar.add(source_dir, arcname=os.path.basename(source_dir))
