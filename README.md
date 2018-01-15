## AWS C Common

Core c99 package for AWS SDK for C. Includes cross-platform primitives, configuration, data structures, and error handling.

## License

This library is licensed under the Apache 2.0 License. 

## Error Codes
The error handling infrastructure is designed to support multiple libraries. For this to work, AWS maintained libraries 
have pre-slotted error codes for each library. The currently allocated error ranges are:

* aws-c-common, [0, 1000)
* aws-c-io, [1000, 2000)
* aws-c-http, [2000, 3000)

Each library should begin its error codes at the beginning of its range and follow in sequence (don't skip codes).
