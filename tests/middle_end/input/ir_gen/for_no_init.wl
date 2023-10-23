//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 0
//       4:   | int t2
//       5:   | t2 = t0 < 10
//       6:   | if t2 != 0 goto L8
//       7:   | jmp L13
//       8:   | int t3
//       9:   | t3 = t0
//      10:   | t3 = t3(@noalias) + 1
//      11:   | t0 = t0(@noalias) + 1(@loop)
//      12:   | jmp L4
//      13:   ret 0
int main() {
    int i = 0;
    int unused = 0;
    for (; i < 10; ++i) {
        int j = i;
        ++j;
    }
    return 0;
}