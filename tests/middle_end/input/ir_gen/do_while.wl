//fun main():
//       0:   alloca int %0
//       1:   store %0 $0
//       2:   alloca int %1
//       3:   store %1 %0
//       4:   store %1 %1 add $1
//       5:   store %0 %0 add $1
//       6:   alloca int %2
//       7:   store %2 %0 lt $10
//       8:   if %2 neq $0 goto L2
//       9:   ret $0
int main() {
    int i = 0;
    do {
        int j = i;
        ++j;
        ++i;
        // Allocate new temporary for comparison there...
    } while (i < 10);
    return 0;
}