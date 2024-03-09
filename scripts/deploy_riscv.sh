# With RVVM image.
sshpass -p riscv scp -Or -P 2022 build/outputs/risc_v root@localhost:/root
sshpass -p riscv scp -Or -P 2022 build/__elf.o root@localhost:/root/risc_v
sshpass -p riscv ssh -p 2022 root@localhost "for f in /root/risc_v/*; do chmod +x \$f; done"