//fun main():
//       0:   int t0(@loop)
//       1:   t0 = 0(@loop)
//       2:   | int t1
//       3:   | t1 = t0 < 10
//       4:   | if t1 != 0 goto L6
//       5:   | jmp L17
//       6:   | int t2(@loop)
//       7:   | t2 = 10(@loop)
//       8:   | | int t3
//       9:   | | t3 = t2 >= 0
//      10:   | | if t3 != 0 goto L12
//      11:   | | jmp L15
//      12:   | | t0 = t0(@noalias) - 1
//      13:   | | t2 = t2(@noalias) - 1(@loop)
//      14:   | | jmp L8
//      15:   | t0 = t0(@noalias) + 1(@loop)
//      16:   | jmp L2
//      17:   ret 0
//--------
//prev(1) = 0
//prev(2) = 1, 16
//prev(3) = 2
//prev(4) = 3
//prev(5) = 4
//prev(6) = 4
//prev(7) = 6
//prev(8) = 7, 14
//prev(9) = 8
//prev(10) = 9
//prev(11) = 10
//prev(12) = 10
//prev(13) = 12
//prev(14) = 13
//prev(15) = 11
//prev(16) = 15
//prev(17) = 5
int main() {
    for (int i = 0; i < 10; ++i) {
        for (int j = 10; j >= 0; --j) {
            --i;
        }
    }
    return 0;
}