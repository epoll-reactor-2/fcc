//3
int main() {
    int    v = 3;
    int  *p0 = &v;
    int **p1 = &p0;

    return **p1;
}