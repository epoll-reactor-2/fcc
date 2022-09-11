// 0
// Actually stub until we cannot cast float to int.
float sqrt(float value) {
    float tmp = 0.0;
    float number = value;
    float root = number / 2.0;

    while (root != tmp) {
        tmp = root;
        float tmp_value = number / tmp;
        tmp_value += tmp;
        tmp_value /= 2.0;
        root = tmp_value;
    }

    return root;
}

int main() {
    float f = sqrt(81.0);
    return 0;
}
