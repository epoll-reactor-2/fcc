//E<7:11>: Expected integer as array index, got char
int main() {
    int array[100];
    int index = 2;
    char wrong_index = 'a';
    array[index] = 0;
    array[wrong_index] = 1;
    return 0;
}
