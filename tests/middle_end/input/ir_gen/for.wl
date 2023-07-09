//fun main():
//       0:   alloca int %0
//       1:   store %0 $0
//       2:   alloca int %1
//       3:   alloca int %2
//       4:   store %2 %0 lt $10
//       5:   alloca int %3
//       6:   store %3 %0 lt $100
//       7:   store %1 %2 or %3
//       8:   if %1 neq $0 goto L10
//       9:   jmp L15
//      10:   alloca int %4
//      11:   store %4 %0
//      12:   store %4 %4 add $1
//      13:   store %0 %0 add $1
//      14:   jmp L2
//      15:   ret $0
int main() {
    for (int i = 0; i < 10 || i < 100; ++i) {
        int j = i;
        ++j;
    }
    return 0;
}