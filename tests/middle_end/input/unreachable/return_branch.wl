//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   int t1
//       3:   t1 = 1
//       4:   int t2
//       5:   t2 = 2
//       6:   | if 0 != 0 goto L8
//       7:   | jmp L10
//       8:   | ret 1
//      10:   | ret 2
int main() {
    int a = 0;
    int b = 1;
    int c = 2;
    if (0) {
        return 1;
    } else {
        return 2;
    }
    return 3;
}