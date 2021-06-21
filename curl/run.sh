#!/bin/bash

http_https="https://"
config_file="audit.csv"
output_folder="output"



function usage()
{
    echo
    echo "##### Housley Audit #####"
    echo ""
    echo "-h --help"
    echo "-a apic_address - Required"
    echo "-u username (default: admin)"
    echo "Password Prompted"
    echo ""
}


PARAMS=""
while (( "$#" )); do
  case "$1" in
    -h|--help)
      usage
      exit 1
      ;;
    -a|--apic_ip)
      if [ -n "$2" ] && [ ${2:0:1} != "-" ]; then
        shift
        apic_ip=$1
      else
        echo "Error: Argument for $1 is missing" >&2
        exit 1
      fi
      ;;
    -u|--username)
      if [ -n "$2" ] && [ ${2:0:1} != "-" ]; then
        shift
        username=$1
      else
        echo "Error: Argument for $1 is missing" >&2
        exit 1
        shift
      fi
      ;;
    -*|--*=) # unsupported flags
      echo "---Error--- Unsupported flag $1" >&2
      usage
      exit 1
      ;;
    *) # preserve positional arguments
      PARAMS="$PARAMS $1"
      shift
      ;;
  esac
  shift
done

# set positional arguments in their proper place
eval set -- "$PARAMS"


### Check variables defined ###
if [ -z "$apic_ip" ]; then
  echo "---ERROR--- -a is not defined"
  usage
  exit 1
fi

if [ -z "$username" ]; then
  username="admin"
  echo "  Username (default): $username"
fi



### Get and check Password ###
echo -n Enter Password:
read -s password
echo

if [ -z "$password" ]; then
  echo "---Error--- Password blank"
  echo
  exit 1
fi

echo

################################################################################


### Create output Directory ###
echo "Creating output directory - $output_folder"
if [[ ! -e $output_folder ]]; then
    mkdir $output_folder
    echo "  Done"
elif [[ ! -d $output_folder ]]; then
    echo "  Exists but not a directory" 1>&2
else
    echo "  Already Exists"
fi


################################################################################


### Login to APIC and create COOKIE ###
echo
echo "### Logging into ACI ###"
curl -sSk -X POST -d "<aaaUser name=$username pwd=$password/>" -c ACI_COOKIE_FILE  $apic_ip/api/mo/aaaLogin.xml 1> /dev/null



if [ -f ./ACI_COOKIE_FILE ]; then
   echo "  Cookie created successfully"
else
   echo "---Error--- Check APIC hostname or credentials"
   exit 1
fi


### Collect Data from ACI ###
echo
echo "### Collecting Data ###"



while IFS=";" read -r url_var name_var dud
do
  echo "Extracting - $name_var - $url_var"
  curl -sSk -X GET -b ACI_COOKIE_FILE -o $output_folder/$name_var --create-dirs $http_https$apic_ip$url_var
  echo "  Done"
done < $config_file



### DELETE COOKIE ###
echo
echo "### Deleting Cookie ###"
rm ACI_COOKIE_FILE
echo "  Done"
echo
echo
echo
