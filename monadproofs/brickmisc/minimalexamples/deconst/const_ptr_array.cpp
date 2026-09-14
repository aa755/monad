namespace minimalexamples
{
    using byte = unsigned char;

    void init_const_input_array(byte const *src, byte const **dst)
    {
        byte const *inputs[1];
        inputs[0] = src;
        *dst = inputs[0];
    }
}
