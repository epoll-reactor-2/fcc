//fun main():
//       0:   alloca int %0
//       1:   store %0 $0
//       2:   alloca int %1
//       3:   store %1 $0
//       4:   alloca int %2
//       5:   store %2 %0 lt $10
//       6:   if %2 neq $0 goto L8
//       7:   jmp L13
//       8:   alloca int %3
//       9:   store %3 %0
//      10:   store %3 %3(@noalias) add $1
//      11:   store %0 %0(@noalias) add $1(@loop)
//      12:   jmp L4
//      13:   ret $0
int main() {
    int i = 0;
    int unused = 0;
    for (; i < 10; ++i) {
        int j = i;
        ++j;
    }
    return 0;
}