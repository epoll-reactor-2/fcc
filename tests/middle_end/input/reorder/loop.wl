//fun main():
//       0:   int t0
//       4:   int t2(@loop)
//       6:   int t3
//       7:   int t4
//       8:   int t5
//      14:   int t6
//      21:   int t7
//       2:   int t1
//       1:   t0 = 0
//       3:   t1 = 0
//       5:   t2 = 0(@loop)
//       9:   t5 = 20 + 30
//      10:   t4 = 10 + t5
//      11:   t3 = t2 < t4
//      12:   if t3 != 0 goto L14
//      13:   jmp L25
//      15:   t6 = t1 == 0
//      16:   if t6 != 0 goto L18
//      17:   jmp L20
//      18:   t0 = t0(@noalias) + 1
//      19:   jmp L21
//      20:   t0 = t0(@noalias) - 1
//      22:   t7 = t0 <<= 1
//      23:   t2 = t2(@noalias) + 1(@loop)
//      24:   jmp L6
//      25:   ret t0
int main() {
    int result = 0;
    int tmp = 0;

    for (int i = 0; i < 10 + 20 + 30; ++i) {
        if (tmp == 0) {
            ++result;
        } else {
            --result;
        }

        result <<= 1;
    }

    return result;
}