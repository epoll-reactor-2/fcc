//fun main():
//       0:   alloca int %0
//       1:   store %0 $0(@loop)
//       2:   alloca int %1
//       3:   store %1 %0
//       4:   store %1 %1(@noalias) add $1
//       5:   store %0 %0(@noalias) add $1(@loop)
//       6:   jmp L2
//       7:   ret $0
int main() {
    for (int i = 0; ; ++i) {
        int j = i;
        ++j;
    }
    return 0;
}