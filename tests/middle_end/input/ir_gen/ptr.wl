//fun main():
//       0:   int t0
//       1:   t0 = 0
//       2:   int * t1
//       3:   t1 = &t0
//       4:   ret *t1
int main() {
    int   a = 0;
    int  *b = &a;

    return *b;
}