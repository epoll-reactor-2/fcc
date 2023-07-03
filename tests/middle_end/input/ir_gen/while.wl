//fun main():
//       0:   alloca int %0
//       1:   store %0 $0
//       2:   alloca int %1
//       3:   store %1 %0 lt $10
//       4:   if %1 neq $0 goto L6
//       5:   jmp L11
//       6:   alloca int %2
//       7:   store %2 %0
//       8:   store %2 %2 add $1
//       9:   store %0 %0 add $1
//      10:   jmp L4
//      11:   ret $0
int main() {
    int i = 0;
    while (i < 10) {
        int j = i;
        ++j;
        ++i;
    }
    return 0;
}