#!/bin/bash

exDir="$1"

bash getAllAttacks.sh "${exDir}"
python3 genCoqProject.py "${exDir}"