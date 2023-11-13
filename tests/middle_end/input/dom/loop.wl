//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 0
//       4:   | int t2
//       5:   | t2 = t1 < 2
//       6:   | if t2 != 0 goto L8
//       7:   | jmp L11
//       8:   | t0 = t0 + 1
//       9:   | t1 = t1 + 1
//      10:   | jmp L4
//      11:   ret t0
//--------
//idom(0) = 0
//idom(1) = 0
//idom(2) = 1
//idom(3) = 2
//idom(4) = 3
//idom(5) = 4
//idom(6) = 5
//idom(7) = 6
//idom(8) = 6
//idom(9) = 8
//idom(10) = 9
//idom(11) = 7
int main() {
    int r = 0;
    for (int i = 0; i < 2; ++i) {
        ++r;
    }
    return r;
}