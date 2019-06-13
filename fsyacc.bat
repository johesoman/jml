@echo off

packages\FsLexYacc\build\fsyacc.exe ParserImpl.fsy

if %errorlevel% == 0 (
  copy ParserImpl.fs temp.txt
  del  ParserImpl.fs
  echo module ParserImpl > ParserImpl.fs
  type temp.txt >> ParserImpl.fs
  del  temp.txt
  pause
)
