import struct

# Assuming you have an array of uint8s like this
uint8_array = [0, 22, 3, 3, 0, 53, 0, 1, 0, 0, 48, 3, 3, 70, 102, 1, 187, 138, 123, 216, 22, 48, 35, 65, 204, 112, 79, 140, 57, 65, 139, 49, 203, 56, 12, 103, 170, 158, 183, 227, 187, 0, 0, 2, 19, 2, 19, 1, 0, 0, 1, 0, 43, 0, 4, 0, 1, 3, 4]

# Convert the array to binary data
binary_data = struct.pack('B' * len(uint8_array), *uint8_array)

# Write the binary data to a file
with open('output.bin', 'wb') as file:
    file.write(binary_data)
