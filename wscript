#! /usr/bin/env python


def options(opts):
    opts.load("compiler_cxx bison flex")


def configure(conf):
    conf.load("compiler_cxx bison flex")
    for arg in ['--cxxflags', '--ldflags', '--libs core', '--system-libs']:
        conf.check_cfg(path='llvm-config', args=arg,
                       package='', uselib_store='LLVM')

    conf.check_cxx(
        uselib_store='ASAN',
        cxxflags=['-fsanitize=address', '-std=c++14',
                  '-fno-omit-frame-pointer'],
        ldflags=['-fsanitize=address']
    )
    conf.load("clang_compilation_database", tooldir="./tools/")


def build(bld):
    bld.stlib(
        source=bld.path.ant_glob('src/*.(l|cc|yc)'),
        target='goat',
        includes='src',
        use='LLVM ASAN'
    )

    bld.recurse('test')
