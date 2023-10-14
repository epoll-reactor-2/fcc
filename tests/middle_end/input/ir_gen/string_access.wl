//fun main():
//       0:   char t0[4]
//       1:   t0 = "abc"
//       2:   char * t1
//       3:   t1 = t0 + 0
//       4:   *t1 = 'a'
//       5:   char * t2
//       6:   t2 = t0 + 1
//       7:   *t2 = 'b'
//       8:   char * t3
//       9:   t3 = t0 + 2
//      10:   char * t4
//      11:   t4 = t0 + 1
//      12:   *t3 = *t4
//      13:   ret 0
int main() {
    char *str = "abc";
    str[0] = 'a';
    str[1] = 'b';
    str[2] = str[1];
    return 0;
}