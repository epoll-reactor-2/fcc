//fun main():
//       0:   if $1 neq $0 goto L2
//       1:   jmp L12
//       2:   if $2 neq $0 goto L4
//       3:   jmp L6
//       4:   ret $3
//       5:   jmp L11
//       6:   if $4 neq $0 goto L8
//       7:   jmp L10
//       8:   ret $5
//       9:   jmp L11
//      10:   ret $6
//      11:   jmp L13
//      12:   ret $7
//      13:   ret $8
int main() {
    if (1) {
        if (2) {
            return 3;
        } else {
            if (4) {
                return 5;
            } else {
                return 6;
            }
        }
    } else {
        return 7;
    }
    return 8;
}