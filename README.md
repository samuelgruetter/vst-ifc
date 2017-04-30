# Information-flow control on top of the Verified Software Toolchain

## How to build

### Get and build VST

    git clone git@github.com:PrincetonUniversity/VST.git
    cd VST
    git checkout HASH

where `HASH` is the commit hash in the file `./VST_VERSION`.

Calculate VST's file dependencies (ignore all the warnings):

    make depend

Build VST (the number after `-j` is the number of cores to use)

    make -j8 floyd


### Build vst-ifc

In the `vst-ifc` directory, create a file called `CONFIGURE` with a line of the form

    VSTDIR=path/to/the/VST/directory

Then run

    make depend
    make examples


### Editing files in CoqIde

    make .loadpath
    coqide `cat .loadpath` path/to/file/to/edit.v

