//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   | if 1 != 0 goto L4
//       3:   | jmp L6
//       4:   | t0 = 1
//       5:   | jmp L7
//       6:   | t0 = 2
//       7:   ret t0
//--------
//idom(0) = 0
//idom(1) = 0
//idom(2) = 1
//idom(3) = 2
//idom(4) = 2
//idom(5) = 4
//idom(6) = 3
//idom(7) = 2
int main() {
    int r = 0;
    if (1) {
        r = 1;
    } else {
        r = 2;
    }
    return r;
}