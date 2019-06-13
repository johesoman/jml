#!/usr/bin/env bash

mono packages/FsLexYacc/build/fsyacc.exe ParserImpl.fsy
sed -i "1i module ParserImpl" ParserImpl.fs
