#!/bin/bash

exDir="$1"
pathToEx="../${exDir}"

for file in "${pathToEx}/chase-inputs"/*
do
  filename="${file##*/}"
  extension="${filename##*.}"
  name="${filename%.*}"
    if [[ "$extension" == "cop" ]]; then
    bash getAttacks.sh "${name}" "${pathToEx}"
  fi
done