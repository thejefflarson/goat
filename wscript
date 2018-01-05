#! /usr/bin/env python


def options(opts):
    """Load up options"""
    opts.load("compiler_cxx bison flex")


def configure(conf):
    """Check that we have a goode compiler and related tools"""
    conf.load("compiler_cxx bison flex")
    for arg in ['--cxxflags', '--ldflags', '--libs core', '--system-libs']:
        conf.check_cfg(path='llvm-config', args=arg,
                       package='', uselib_store='LLVM')

    conf.env['CXXFLAGS_LLVM'].remove('-std=c++11')
    conf.env['CXXFLAGS_LLVM'].append('-I./deps/GSL/include')

    conf.check_cxx(
        uselib_store='ASAN',
        cxxflags=[#'-fsanitize=address',
            '-std=c++17',
            '-g',
            '-O0',
            '-fno-omit-frame-pointer'
        ]#,
        #ldflags=['-fsanitize=address']
    )
    conf.load("clang_compilation_database", tooldir="./tools/")


def build(bld):
    """Build the thing"""
    bld.stlib(
        source=bld.path.ant_glob('src/*.(l|cc|yc)'),
        target='goat',
        includes=['src', 'deps/GSL/include'],
        use='LLVM ASAN'
    )

    bld.recurse('test')
