//fun main():
//       0:   int t0
//       1:   t0 = 5
//       2:   | if t0 != 0 goto L4
//       3:   | jmp L11
//       4:   | int t1
//       5:   | t1 = 10
//       6:   | | if t1 != 0 goto L8
//       7:   | | jmp L9
//       8:   | | jmp L6
//       9:   | t0 = t0(@noalias) - 1
//      10:   | jmp L2
//      11:   ret t0
//--------
//prev(1) = 0
//prev(2) = 1, 10
//prev(3) = 2
//prev(4) = 2
//prev(5) = 4
//prev(6) = 5, 8
//prev(7) = 6
//prev(8) = 6
//prev(9) = 7
//prev(10) = 9
//prev(11) = 3
int main() {
    int i = 5;
    while (i) {
        int j = 10;
        while (j)
            {}
        --i;
    }
    return i;
}