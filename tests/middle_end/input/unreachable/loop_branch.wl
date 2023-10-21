//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = 2
//       4:   if t0 != 0 goto L6
//       5:   jmp L9
//       6:   ret 1
//       9:   if t1 != 0 goto L11
//      10:   jmp L17
//      11:   t1 = t1(@noalias) - 1
//      12:   if t0 != 0 goto L14
//      13:   jmp L15
//      14:   ret 2
//      15:   t1 = t1(@noalias) + 1
//      16:   jmp L9
//      17:   ret 0
int main() {
    int a = 1;
    int b = 2;
    if (a) {
        return 1;
        ++a;
    } else {
        while (b) {
            --b;
            if (a) {
                return 2;
            }
            ++b;
        }
    }
    return 0;
}