from PIL import Image
import math
import sys

if len(sys.argv) > 1:
    filename = sys.argv[1]
    im = Image.open(filename)
    print(f"{im.height} {im.width}")
    for y in range(im.height):
        for x in range(im.width):
            (r,g,b,_) = im.getpixel((x, y))
            brightness = math.sqrt(0.241*(r**2) + 0.691*(g**2) + 0.068*(b**2))
            if brightness < 240:
                print("1", end="")
            else:
                print("0", end="")
        print()
