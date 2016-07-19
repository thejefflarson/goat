#! /usr/bin/env python


def options(opts):
    opts.load("compiler_cxx bison flex")


def configure(conf):
    conf.load("compiler_cxx bison flex")


def build():
    pass


def test():
    pass
