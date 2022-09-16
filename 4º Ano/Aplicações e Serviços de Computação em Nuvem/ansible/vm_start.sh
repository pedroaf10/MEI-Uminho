#!/bin/sh
sudo add-apt-repository --yes --update ppa:ansible/ansible
sudo apt-get update
sudo apt-get install -y ansible
gcloud auth activate-service-account service-account --key-file=$HOME/ansible/service_account_credentials.json --project=project-name