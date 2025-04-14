#!/bin/bash

name="$1"
pathToEx="$2"


# Run Chase
make "${name}_chase.xhtml" -C "${pathToEx}/chase-inputs/" -f Makefile.chase

# Move Chase output to chase-outputs directory
mv "${pathToEx}/chase-inputs/${name}_chase.xhtml" "${pathToEx}/chase-outputs/"

# Remove XML version duplicate 
# Otherwise there is an XML parsing error
sed -i 's,<?xml version="1.0" encoding="UTF-8" standalone="no"?>, ,' "${pathToEx}/chase-outputs/${name}_chase.xhtml"
sed -i 's,<!DOCTYPE svg PUBLIC "-//W3C//DTD SVG 1.1//EN", ,' "${pathToEx}/chase-outputs/${name}_chase.xhtml"
sed -i 's,"http://www.w3.org/Graphics/SVG/1.1/DTD/svg11.dtd">, ,' "${pathToEx}/chase-outputs/${name}_chase.xhtml"

# Reduce Chase output to contain only the attack graphs
sed '1,/>Models</d' "${pathToEx}/chase-outputs/${name}_chase.xhtml" > "${pathToEx}/chase-outputs/${name}_graphs.xhtml"

# Convert attack graphs in XHTML to Coq
python3 xhtml2coq.py "${name}" "${pathToEx}/chase-outputs"

# Move attack graphs in Coq to examples directory
mv "${pathToEx}/chase-outputs/${name}.v" "${pathToEx}/"

# Remove temporary file containing attack graphs in XHTML
rm "${pathToEx}/chase-outputs/${name}_graphs.xhtml"