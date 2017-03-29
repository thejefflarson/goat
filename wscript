#! /usr/bin/env python


def options(opts):
    opts.load("compiler_cxx bison flex")


def configure(conf):
    conf.load("compiler_cxx bison flex")
    conf.check_cxx(
        uselib_store='G',
        cxxflags=['-std=c++14', '-g', '-Wall', '-O0',
                  '-fsanitize=address',
                  '-fno-omit-frame-pointer'],
        ldflags=['-fsanitize=address']
    )
    conf.load("clang_compilation_database", tooldir="./tools/")


def build(bld):
    bld.stlib(
        source=bld.path.ant_glob('src/*.(l|cc|yc)'),
        target='goat',
        includes='src',
        use='G'
    )

    bld.recurse('test')
