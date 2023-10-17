//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   if t0 != 0 goto L4
//       3:   jmp L8
//       4:   t0 = t0(@noalias) + 1
//       5:   jmp L2
//       8:   ret 0
int main() {
    int a = 1;
    while (a) {
        ++a;
        continue;
        --a;
    }
    return 0;
}