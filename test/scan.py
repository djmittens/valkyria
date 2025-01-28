#!/usr/bin/env python3.11

import pycparser
from  pycparser import parse_file
import pycparser_fake_libc
import os


print(pycparser_fake_libc.directory)

ast = parse_file("test/test_parser.c", use_cpp=True,
    cpp_path='clang',
    cpp_args=['-E', r'-I{}'.format(pycparser_fake_libc.directory), '-Isrc', '-Itest'])
ast.show()
