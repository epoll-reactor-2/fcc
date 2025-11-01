make || exit
(cd build; LD_LIBRARY_PATH=./lib ./bin/ssa_test)

for f in build/outputs/ssa/*.dot; do
    echo "Creating $f.png..."
    dot -Tpng $f > $f.png
done

swiv build/outputs/ssa/*.png
