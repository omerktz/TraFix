import boto3
import paramiko
import os
import parmap

ec2 = boto3.client('ec2')

def handle_instance((dns,i)):
	client = paramiko.SSHClient()
	client.set_missing_host_key_policy(paramiko.AutoAddPolicy)
	client.connect(dns, username='ubuntu', key_filename='omer1.pem')
	sin, sout, serr = client.exec_command('cd Codenator; tar -xzf tmp.tar.gz output* log*')
	sout.channel.recv_exit_status()
	sftp = client.open_sftp()
	sftp.chdir('Codenator')
	sftp.get('tmp.tar.gz', os.path.join('downloaded_x86', 'tmp{0}.tar.gz'.format(i)))
	sin, sout, serr = client.exec_command('cd Codenator; rm tmp.tar.gz')
	sout.channel.recv_exit_status()
	client.close()

dnss = map(lambda y: y['Instances'][0]['PublicDnsName'], filter(lambda x: x['Instances'][0]['Tags'][0]['Value'].startswith('omer-x86'), ec2.describe_instances()['Reservations']))
parmap.map(handle_instance, map(lambda i: (dnss[i], i), range(len(dnss))))
