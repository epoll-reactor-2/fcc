//fun main():
//       0:   int t0
//       4:   int t2(@loop)
//       6:   int t3
//       7:   int t4
//       8:   int t5
//      14:   int t6
//      15:   int t7
//      16:   int t8
//      17:   int t9
//      27:   int t10
//       2:   int t1
//       1:   t0 = 0
//       3:   t1 = 0
//       5:   t2 = 0(@loop)
//       9:   | t5 = 20 + 30
//      10:   | t4 = 10 + t5
//      11:   | t3 = t2 < t4
//      12:   | if t3 != 0 goto L18
//      13:   | jmp L31
//      18:   | | t9 = 2 + 3
//      19:   | | t8 = 1 + t9
//      20:   | | t7 = t1 + t8
//      21:   | | t6 = t7 == 0
//      22:   | | if t6 != 0 goto L24
//      23:   | | jmp L26
//      24:   | | t0 = t0(@noalias) + 1
//      25:   | | jmp L29
//      26:   | | t0 = t0(@noalias) - 1
//      28:   | t10 = t0 <<= 1
//      29:   | t2 = t2(@noalias) + 1(@loop)
//      30:   | jmp L10
//      31:   ret t0
int main() {
    int result = 0;
    int tmp = 0;

    for (int i = 0; i < 10 + 20 + 30; ++i) {
        if (tmp + 1 + 2 + 3 == 0) {
            ++result;
        } else {
            --result;
        }

        result <<= 1;
    }

    return result;
}