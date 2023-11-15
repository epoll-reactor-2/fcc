//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   int * t1
//       3:   int t2
//       4:   t2 = t0
//       5:   t1 = &t2
//       6:   int * t3
//       7:   t3 = t1
//       8:   ret *t3
int main() {
    int   a = 0;
    int  *b = &a;

    return *b;
}