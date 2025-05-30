#!/bin/bash
#
# File:  mk_config.sh
# Author:  mikolas
# Created on:  Mon Jun 17 20:34:57 CEST 2024
# Copyright (C) 2024, Mikolas Janota
#

fst=true
echo '{' >config.json
echo '"parallel_timeout" : 120,' >>config.json
echo -n '"parallel": 1,' >>config.json
for prg in 'z3' 'cvc5' 'tarski' 'vampire'; do
    P=`which "$prg"`
    if [ $? == 0 ]; then
        if $fst ; then
          echo ""
        else
          echo ","
        fi
        echo -n '"'${prg}'"' : '"'${P}'"'
        fst=false
    else
        echo failure on "$prg" >&2
    fi
done >>config.json
echo '}' >>config.json
