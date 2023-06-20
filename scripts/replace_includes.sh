for f in `find lib tests -name '*.c' -o -name '*.h'`; do sed -i 's/#include\ \"utility/#include \"util/g' $f; done
