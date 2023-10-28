//fun main():
//       0:   int t0
//       1:   t0 = 0
//       4:   | if t0 != 0 goto L6
//       5:   | jmp L27
//       6:   | int t2(@loop)
//       7:   | t2 = 0(@loop)
//       8:   | | int t3
//       9:   | | t3 = t2 & 5
//      10:   | | if t3 != 0 goto L12
//      11:   | | jmp L26
//      12:   | | | int t4
//      13:   | | | int t5
//      14:   | | | t5 = 2 + 3
//      15:   | | | t4 = t2 < t5
//      16:   | | | if t4 != 0 goto L18
//      17:   | | | jmp L20
//      18:   | | | t0 = t0(@noalias) - 1
//      19:   | | | jmp L23
//      20:   | | | int t6
//      21:   | | | t6 = t0(@noalias) & 1
//      22:   | | | t0 = t6
//      23:   | | int t7(@loop)
//      24:   | | t7 = t2 <<= 1(@loop)
//      25:   | | jmp L8
//      26:   | jmp L4
//      35:   ret t0
int main() {
    int i = 0;
    int j = 0;

    while (i) {
        for (int x = 0; x & 5; x <<= 1) {
            if (x < 2 + 3) {
                --i;
            } else {
                i = i & 1;
            }
        }
    }

    while (j) {
        ++j;
        j = j << 1;
        --j;
    }

    return i;
}