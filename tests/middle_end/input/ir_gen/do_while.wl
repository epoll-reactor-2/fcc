//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   | int t1
//       3:   | t1 = t0
//       4:   | t1 = t1(@noalias) + 1
//       5:   | t0 = t0(@noalias) + 1
//       6:   | int t2(@loop)
//       7:   | t2 = t0 < 10(@loop)
//       8:   | if t2 != 0 goto L2
//       9:   ret 0
int main() {
    int i = 0;
    do {
        int j = i;
        ++j;
        ++i;
    } while (i < 10);
    return 0;
}