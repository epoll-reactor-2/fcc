//E<22:17>: Indirection level mismatch (0 vs 1)
int f(int ***arg_0)
{
    int **arg_1 = *arg_0;
    int  *arg_2 = *arg_1;

    return *arg_2;
}

int *ptr(int *arg_0)
{
    return arg_0;
}

int main()
{
    int    a =  0;
    int   *b = &a;
    int  **c = &b;
    int ***d = &c;

    return f(d) + ptr(b);
}