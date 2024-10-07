//...
int f_1() { return 1; }
int f_2() { return 2; }
int f_3() { return f_2(); }

int main()
{
    f_1();
    return 0;
}

int f_4() { return f_3(); }