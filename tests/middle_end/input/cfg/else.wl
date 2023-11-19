//fun main():
//       0:   | if 1 != 0 goto L2
//       1:   | jmp L4
//       2:   | ret 2
//       3:   | jmp L5
//       4:   | ret 3
//       5:   ret 4
//--------
//  0: cfg = 0, next = (2, 1)
//  1: cfg = 1, prev = (0), next = (4)
//  2: cfg = 2, prev = (0)
//  3: cfg = 2, prev = (2), next = (5)
//  4: cfg = 3, prev = (1)
//  5: cfg = 3, prev = (3)
int main() {
    if (1) {
        return 2;
    } else {
        return 3;
    }
    return 4;
}