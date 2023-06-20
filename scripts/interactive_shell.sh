if ! test -f Compiler; then
	echo "Required 'Compiler' binary"
	exit 1
fi

echo "Type empty line to compile and show LLVM IR"

while :; do
	echo "> "
	line="~"
	until [ "$line" = "" ]
	do
	   read line
	   echo $line >> input.wl
	done
	./Compiler -i input.wl -dump-llvm
	rm -rf input.wl
done
