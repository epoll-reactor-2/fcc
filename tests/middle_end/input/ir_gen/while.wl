//fun main():
//       0:   alloca int %0
//       1:   store %0 $1
//       2:   alloca int %1(@loop)
//       3:   alloca int %2(@loop)
//       4:   store %2 %0 lt $10(@loop)
//       5:   alloca int %3(@loop)
//       6:   store %3 %0 neq $0(@loop)
//       7:   store %1 %2 and %3(@loop)
//       8:   if %1 neq $0 goto L10
//       9:   jmp L15
//      10:   alloca int %4
//      11:   store %4 %0
//      12:   store %4 %4(@noalias) add $1
//      13:   store %0 %0(@noalias) add $1
//      14:   jmp L2
//      15:   ret $0
int main() {
    int i = 1;
    while (i < 10 && i != 0) {
        int j = i;
        ++j;
        ++i;
    }
    return 0;
}