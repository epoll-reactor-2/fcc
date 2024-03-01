make clean
make
pushd build
./elf_test
chmod +x ./__elf.o
gdb ./__elf.o
popd build