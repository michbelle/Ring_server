tar -xf ringserver-2020.075.tar
tar -xzf slink2dali-0.7.tar.gz

#il primo lancio non necessità di questo
#source bin/stop.sh

#rm bin/ringserver
#rm bin/slink2dali

cd ringserver-2020.075
#rm ringserver
make
cp ringserver ../bin/
cd ..


cd slink2dali
#rm slink2dali
make
cp slink2dali ../bin/

cd ../bin/
source start.sh
