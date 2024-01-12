pvs-studio-analyzer trace -- make
pvs-studio-analyzer analyze -j8
plog-converter -a GA:1,2 -t json -o PVS-Studio-Report.json PVS-Studio.log