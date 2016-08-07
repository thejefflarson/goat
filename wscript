#! /usr/bin/env python


def options(opts):
    opts.load("compiler_cxx bison flex")


def configure(conf):
    conf.load("compiler_cxx bison flex")
    conf.check_cxx(uselib_store='G', cxxflags='-std=c++14')


def build(bld):
    bld.shlib(
        source=bld.path.ant_glob('src/*.(l|cc|yc)'),
        target='goat',
        includes='src',
        use='G'
    )

    #bld.recurse('test')
