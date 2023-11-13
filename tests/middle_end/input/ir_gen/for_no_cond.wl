//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   | int t1
//       3:   | t1 = t0
//       4:   | t1 = t1 + 1
//       5:   | t0 = t0 + 1
//       6:   | jmp L2
//       7:   ret 0
int main() {
    for (int i = 0; ; ++i) {
        int j = i;
        ++j;
    }
    return 0;
}