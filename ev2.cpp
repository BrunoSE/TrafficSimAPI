#include <stdlib.h>
#include <stdio.h>
#include <string>
#include <math.h>
#include "programmer.h"
#include <time.h>
#include <map>
#include <vector>
#include <random>
#include<iostream>
#include<fstream>
//Por Bruno Stefoni para Tesis Simulacion de operacion de Vehiculos de Emergencia - enero-diciembre 2016

std::random_device rd;
std::mt19937 gen(rd());
std::uniform_real_distribution<> dis(0, 1);

//Modelo asume a lo mas 5 pistas en cualquier arco
#define n_max_pistas 6
//EV son tipo vehiculo 10 en Modeller de Paramics
#define n_tipo_EV 10
//Tipos que usan pistas exclusivas
#define n_tipo_Bus1 16
#define n_tipo_Bus2 15
#define n_tipo_Taxi 3
//Largo de un EV es 11.5 metros en Modeller de Paramics
#define largo_EV 11.5
//Agresion maxima de modelo Paramics es 8
#define max_agresion 8
//Timesteps atras que vehiculo considera para calcular su velocidad promedio
#define segundos_velocidad_historica 60

//Mapa con true/false si vehiculo esta alerta o no
std::map<int, Bool[2]> map_veh_alerta; //index viene de VEHICLE*
//Mapa que guarda agresividades
std::map<int, int> map_agresividades; //index viene de VEHICLE*

//Mapa que cuenta timestep de vehiculo buscando cambiarse de pista para dar paso a EV
std::map<int, int> contador_timesteps_intentando_cambiarse_pista; //index viene de VEHICLE*
//Mapa que guarda EV lider de timestep anterior
std::map<int, VEHICLE*> map_EV_lider_timestep_anterior; //index viene de LINK*

//Mapa con true/false si vehiculo quiere subirse a vereda
std::map<int, Bool[2]> map_veh_quiere_vereda; //index viene de VEHICLE*
//Mapas que cuentan timestep para eventos en modelo de vereda
std::map<int, int> contador_timesteps_intentando_subirse_vereda; //index viene de VEHICLE*
//Mapa de velocidades historicas en "ultimos segundos_velocidad_historica" segundos
std::map<int, std::pair<int, std::vector<float> >> map_velocidades_historicas; //index viene de VEHICLE*
//Mapa que guarda si vehiculo tiene al menos segundos_velocidad_historica segundos de existencia
std::map<int, std::pair<int, Bool>> map_veh_tiene_suficiente_tiempo; //index viene de VEHICLE*

//Mapa con true/false si link en su nodo final tiene interseccion
std::map<int, Bool> map_link_tiene_interseccion; //index viene de LINK*
//Mapa con true/false si se debe ceder el paso a EV en interseccion al final del link
std::map<int, Bool> map_link_cede_interseccion; //index viene de LINK*
//Mapa con true/false si EV esta cruzando interseccion
std::map<int, Bool> map_EV_cruzando_interseccion; //index viene de VEHICLE*
//Mapa con nodo de interseccion donde paso EV en el pasado (volver link entrantes al nodo a normalidad) 
std::map<int, NODE*> map_link_anterior_EV_cruzando_interseccion; //index viene de VEHICLE*

//Cantidad de timesteps que ocurren en simulacion por cada segundo
int timesteps_por_segundo;

//Metros aguas abajo y aguas arriba que autos se preocupan por EV
const float distancia_alerta_aguas_abajo = 35;
const float distancia_alerta_aguas_arriba = 5;
//Tolerancia para mapa que cuenta segundo buscando cambiarse de pista para dar paso a EV
const int tolerancia_segundos_intentando_cambiarse_pista = 1;
const int tolerancia_segundos_volver_cambiarse_pista = 5;

//Metros aguas abajo que autos se preocupan por EV para subirse a vereda
const float distancia_alerta_aguas_abajo_vereda = 35;

//Tolerancia para los mapas que cuentan segundos buscando subir a vereda
const int tolerancia_segundos_buscando_subir_vereda = 1;
const int tolerancia_segundos_volver_subir_vereda = 5;

//Distancia a la intersseccion hasta la que cubre el modelo de vereda
const float distancia_min_interseccion_modelo_vereda = 15;

//Velocidad promedio de ultimo tiempo en la que un vehiculo percibe que debe subirse a vereda
const float velocidad_historica_querer_vereda = 4;

//Distancia a la linea de detencion que EV provoca preocupacion en autos cerca de interseccion
const int distancia_modelo_interseccion = 15;
const int distancia_stop_modelo_interseccion = 3;

//Variables auxiliares que guardan vehiculos y EV
VEHICLE* vehiculo_sgte = NULL;
VEHICLE* EV_lider = NULL;
VEHICLE* EV_lider_anterior = NULL;
VEHICLE* EV_lider_pista[n_max_pistas];

//Indica si hay un EV en la pista o no
Bool EV_en_pista[n_max_pistas];
//Indica si EV lider es distinto que timestep anterior si antes existia un lider
Bool EV_lider_distinto_anterior;

//Distancias de los EV mas cerca y lejos de la linea de detencion en el arco
float dist_min;
float dist_max;
//Distancias de los EV mas cerca y lejos de la linea de detencion por pista en el arco
float distancia_min[n_max_pistas];
float distancia_max[n_max_pistas];

//Numero de pistas del arco a analizar
int n_pistas;
//Numero de pista del EV mas cerca a la linea de detencion
int pista_EV_lider;
//Variable aleatoria binomial
int coin;
//Pista min y max que no son cerradas ni acera
int pista_min;
int pista_max;

//Llamado apenas se carga la red
void qpx_NET_postOpen(void) {

	//Mandar mensaje por tab "Messages", cambiar semilla para generar numeros aleatorios
	qps_GUI_printf("%s\n", "Modelo para Vehiculos de Emergencia");
	//srand(time(NULL)); //cambiar semilla para generar numeros aleatorios

	//Calcular si el nodo "cabeza" de un link es una interseccion o no para todos los links de la red, apenas se abre el programa
	//Para esto ve si: hay más de un acceso a interseccion, o mas de 2 salidas a interseccion
	for (int i = 1; i <= qpg_NET_links(); i++)
	{
		if (qpg_NDE_entryLinks(qpg_LNK_nodeEnd(qpg_NET_linkByIndex(i))) >= 2)
		{
			map_link_tiene_interseccion[qpg_LNK_index(qpg_NET_linkByIndex(i))] = PTRUE;
		}
		else if (qpg_NDE_exitLinks(qpg_LNK_nodeEnd(qpg_NET_linkByIndex(i))) >= 3)
		{
			map_link_tiene_interseccion[qpg_LNK_index(qpg_NET_linkByIndex(i))] = PTRUE;
		}
		else
		{
			map_link_tiene_interseccion[qpg_LNK_index(qpg_NET_linkByIndex(i))] = PFALSE;
		}
	}

	timesteps_por_segundo = int(1 / qpg_CFG_timeStep());
	qps_GUI_printf("Timesteps por segundo: %d\n", int(1 / qpg_CFG_timeStep()));

	//para probrar generado de numeros aleatorios
	//qps_GUI_printf("%f\n", dis(gen));
	//int asdfqwer = dis(gen);
}

//Llamado al recargar la red
void qpx_NET_reload(void) {
	//Liberar memoria
	map_veh_alerta.clear();
	map_agresividades.clear();
	contador_timesteps_intentando_cambiarse_pista.clear();
	map_EV_lider_timestep_anterior.clear();
	map_veh_quiere_vereda.clear();
	contador_timesteps_intentando_subirse_vereda.clear();
	map_velocidades_historicas.clear();
	map_link_cede_interseccion.clear();
	map_EV_cruzando_interseccion.clear();
	map_link_anterior_EV_cruzando_interseccion.clear();
	map_veh_tiene_suficiente_tiempo.clear();

	timesteps_por_segundo = int(1 / qpg_CFG_timeStep());
	//srand(time(NULL)); //cambiar semilla para generar numeros aleatorios
}

//Devuelve maximo entre los n primeros valores de un arreglo
float maximo(float x[], int n) {
	float max = x[0];
	for (int i = 1; i < n; i++)
	{
		if (max < x[i])
		{
			max = x[i];
		}
	}
	return max;
}

//Devuelve minimo entre los n primeros valores de un arreglo
float minimo(float x[], int n) {
	float min = x[0];
	for (int i = 1; i < n; i++)
	{
		if (min > x[i])
		{
			min = x[i];
		}
	}
	return min;
}

//Devuelve indice del arreglo con el valor minimo
int indice_minimo(float x[], int n) {
	float min = x[0];
	int j = 0;
	for (int i = 1; i < n; i++)
	{
		if (min > x[i])
		{
			min = x[i];
			j = i;
		}
	}
	return j;
}

//Devuelve 1 o -1 aleatoriamente
int moneda(void) {
	if (rand() % 2 == 0)
	{
		return 1;
	}
	else
	{
		return -1;
	}
}

//Devuelve promedio de primeros n elementos de un arreglo de floats
float promedio(std::vector<float> x, int n) {
	float r = x[0];
	for (int i = 1; i < n; i++)
	{
		r += x[i];
	}
	return r / n;
}

//Devuelve True si el vehiculo v puede transitar en pista p
Bool puede_usar_pista(VEHICLE* v, LINK* l, int p) {
	if (qpg_LNK_laneRestriction(l, p) == 0)
	{
		return PTRUE;
	}
	else if (qpg_LNK_laneRestriction(l, p) == 1 && (qpg_VHC_type(v) == n_tipo_Taxi || qpg_VHC_type(v) == n_tipo_EV || qpg_VHC_type(v) == n_tipo_Bus1 || qpg_VHC_type(v) == n_tipo_Bus2))
	{
		return PTRUE;
	}
	else if (qpg_LNK_laneRestriction(l, p) == 2 && (qpg_VHC_type(v) == n_tipo_EV || qpg_VHC_type(v) == n_tipo_Bus1 || qpg_VHC_type(v) == n_tipo_Bus2))
	{
		return PTRUE;
	}
	else if (qpg_LNK_laneRestriction(l, p) == 3 && qpg_VHC_type(v) == n_tipo_EV)
	{
		return PTRUE;
	}
	else
	{
		return PFALSE;
	}
}

//Devuelve numero min de pista donde el vehiculo puede transitar
int puede_usar_pista_min(VEHICLE* ve, LINK* li){
	for (int i = 1; i <= qpg_LNK_lanes(li); i++)
	{
		if (puede_usar_pista(ve, li, i) == PTRUE)
		{
			return i;
			break;
		}
	}
	return -1;//no puede usar ninguna
}


//Devuelve numero max de pista donde el vehiculo puede transitar
int puede_usar_pista_max(VEHICLE* ve, LINK* li) {
	for (int i = qpg_LNK_lanes(li); i >= 1; i--)
	{
		if (puede_usar_pista(ve, li, i) == PTRUE)
		{
			return i;
			break;
		}
	}
	return -1; //no puede usar ninguna
}

//Devuelve true si el vehiculo es un automovil privado liviano o bien camion pequeno (de largo 6m a lo mas)
Bool es_veh_liviano(VEHICLE* v)
{
	if (qpg_VHC_type(v) <= 9 )//&& qpg_VHC_type(v) != n_tipo_Taxi)
	{
		return PTRUE;
	}
	else if (qpg_VHC_type(v) == 11)
	{
		return PTRUE;
	}
	else
	{
		return PFALSE;
	}
}

//Llamado cada instante discreto de simulacion sobre cada link
void qpx_LNK_timeStep(LINK* link) {

	//Declaracion de variables
	for (int i = 0; i < n_max_pistas; i++)
	{
		distancia_max[i] = 0;
		distancia_min[i] = qpg_LNK_length(link);
		EV_en_pista[i] = PFALSE;
		EV_lider_pista[i] = NULL;
	}
	n_pistas = qpg_LNK_lanes(link);
	EV_lider = NULL;
	EV_lider_distinto_anterior = PFALSE;
	pista_min = 1;
	pista_max = n_pistas;

	//Buscar si hay EV en pista i, calcular distancia de EVs mas alejado y mas cercano a la salida del link
	for (int i = 0; i < n_pistas; i++)
	{
		vehiculo_sgte = qpg_LNK_vehicleTail(link, i + 1);
		while (vehiculo_sgte != NULL)
		{
			if (qpg_VHC_type(vehiculo_sgte) == n_tipo_EV)
			{
				//todos los EV tienen agresion 8
				qps_VHC_aggression(vehiculo_sgte, max_agresion);

				if (EV_en_pista[i] == PFALSE)
				{
					distancia_max[i] = qpg_VHC_distance(vehiculo_sgte);
				}

				distancia_min[i] = qpg_VHC_distance(vehiculo_sgte);
				EV_en_pista[i] = PTRUE;
				EV_lider_pista[i] = vehiculo_sgte;

			}
			vehiculo_sgte = qpg_VHC_ahead(vehiculo_sgte);
		}
	}

	//Guardar valores min y max de distancia entre todas las pistas
	dist_max = maximo(distancia_max, n_pistas);
	dist_min = minimo(distancia_min, n_pistas);

	//Guardar pista del lider y vehiculo lider
	pista_EV_lider = indice_minimo(distancia_min, n_pistas) + 1; //+1 para pasar de indice a pista
	EV_lider = EV_lider_pista[pista_EV_lider - 1];
	
	//si hay mas de una pista en el arco, ver cuales son transitables (que no es -1 o 4, closed o acera respectivamente)
	if (n_pistas > 1)
	{
		if (qpg_LNK_laneRestriction(link, 1) == -1 || qpg_LNK_laneRestriction(link, 1) == 4)
		{
			pista_min = 2;
		}
		if (qpg_LNK_laneRestriction(link, n_pistas) == -1 || qpg_LNK_laneRestriction(link, n_pistas) == 4)
		{
			pista_max = n_pistas - 1;
		}
	}

	//Si existe algun EV en link
	if (EV_lider != NULL)
	{
		if (pista_max != pista_min)
		{
			//Si EV lider en el link es distinto que timestep anterior y existia un lider antes
			if (map_EV_lider_timestep_anterior[qpg_LNK_index(link)] != NULL && qpg_VHC_uniqueID(map_EV_lider_timestep_anterior[qpg_LNK_index(link)]) != qpg_VHC_uniqueID(EV_lider))
			{
				EV_lider_distinto_anterior = PTRUE;
			}

			//for para cada pista usable para transitar
			for (int j = pista_min; j <= pista_max; j++)
			{
				//while para cada vehiculo en la pista
				vehiculo_sgte = qpg_LNK_vehicleTail(link, j);
				while (vehiculo_sgte != NULL)
				{

					//si esta entre el EV mas lejano y el EV mas cercano a la salida del link o "distancia_alerta" metros aguas abajo de este ultimo
					if (qpg_VHC_distance(vehiculo_sgte) >= distancia_modelo_interseccion && qpg_VHC_distance(vehiculo_sgte) <= dist_max + distancia_alerta_aguas_arriba + largo_EV && qpg_VHC_distance(vehiculo_sgte) >= dist_min - distancia_alerta_aguas_abajo)
					{

						//si es EV
						if (qpg_VHC_type(vehiculo_sgte) == n_tipo_EV)
						{
							//si no es el EV lider
							if (qpg_VHC_uniqueID(vehiculo_sgte) != qpg_VHC_uniqueID(EV_lider) && (map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][1] == PFALSE || EV_lider_distinto_anterior == PTRUE))
							{
								//cambiarse a la pista del lider
								qps_VHC_laneRange(vehiculo_sgte, pista_EV_lider, pista_EV_lider);
								map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PTRUE;
							}

							//si soy el lider y antes no lo era, poder moverme por todas las pistas
							else if (EV_lider_distinto_anterior == PTRUE)
							{
								qps_VHC_laneRange(vehiculo_sgte, pista_min, pista_max);
								map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PFALSE;
							}
						}
						//no soy EV y estoy en pista de EV
						else if (map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][0] == PFALSE && j == pista_EV_lider)
						{
							map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PTRUE;
							qps_VHC_aggression(vehiculo_sgte, max_agresion);

							//Estoy cerca de la vereda y EV lider tambien
							if (j == pista_min)
							{
								//sugerir cambiarse si es bus
								if (qpg_VHC_type(vehiculo_sgte) != n_tipo_Bus1 && qpg_VHC_type(vehiculo_sgte) != n_tipo_Bus2 && puede_usar_pista(vehiculo_sgte, link, j + 1) == PTRUE)
								{
									qps_VHC_laneLow(vehiculo_sgte, j + 1);
								}
							}
							else if (j == pista_max)
							{
								if (puede_usar_pista(vehiculo_sgte, link, j - 1) == PTRUE)
								{
									qps_VHC_laneHigh(vehiculo_sgte, j - 1);
								}
							}

							else if(puede_usar_pista(vehiculo_sgte, link, j - 1) == PTRUE && puede_usar_pista(vehiculo_sgte, link, j + 1) == PTRUE)
							{
								if (qpg_VHC_type(vehiculo_sgte) == n_tipo_Bus1 || qpg_VHC_type(vehiculo_sgte) == n_tipo_Bus2)
								{
									qps_VHC_laneHigh(vehiculo_sgte, j - 1);
								}
								else if (moneda() == 1)
								{
									qps_VHC_laneHigh(vehiculo_sgte, j - 1);
								}
								else
								{
									qps_VHC_laneLow(vehiculo_sgte, j + 1);
								}
							}
							else if (puede_usar_pista(vehiculo_sgte, link, j - 1) == PTRUE)
							{
								qps_VHC_laneHigh(vehiculo_sgte, j - 1);
							}
							else if (puede_usar_pista(vehiculo_sgte, link, j + 1) == PTRUE)
							{
								qps_VHC_laneLow(vehiculo_sgte, j + 1);
							}

							if (map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][1] == PTRUE)
							{
								contador_timesteps_intentando_cambiarse_pista[qpg_VHC_uniqueID(vehiculo_sgte)] += 1;
								if (contador_timesteps_intentando_cambiarse_pista[qpg_VHC_uniqueID(vehiculo_sgte)] >= tolerancia_segundos_intentando_cambiarse_pista*timesteps_por_segundo)
								{
									map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PTRUE;
									map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PFALSE;
									qps_VHC_laneRange(vehiculo_sgte, puede_usar_pista_min(vehiculo_sgte, link), puede_usar_pista_max(vehiculo_sgte, link));
									contador_timesteps_intentando_cambiarse_pista[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
								}
							}
						}

						else if (map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][0] == PTRUE && j == pista_EV_lider)
						{
							contador_timesteps_intentando_cambiarse_pista[qpg_VHC_uniqueID(vehiculo_sgte)] += 1;
							if (contador_timesteps_intentando_cambiarse_pista[qpg_VHC_uniqueID(vehiculo_sgte)] >= tolerancia_segundos_volver_cambiarse_pista*timesteps_por_segundo)
							{
								contador_timesteps_intentando_cambiarse_pista[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
								map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PFALSE;
							}
						}

						else if (j != pista_EV_lider)
						{
							//Estar alerta y agresividad maxima
							contador_timesteps_intentando_cambiarse_pista[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
							map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PFALSE;
							map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PTRUE;
							qps_VHC_aggression(vehiculo_sgte, map_agresividades[qpg_VHC_uniqueID(vehiculo_sgte)]);

							//si pudiese interferir paso de EV
							if (puede_usar_pista(vehiculo_sgte, link, pista_EV_lider) == PTRUE)
							{
								//si estoy 1 pista a la derecha del EV
								if (pista_EV_lider - j == 1)
								{
									qps_VHC_laneHigh(vehiculo_sgte, j);
								}
								//si estoy 1 pista a la izquierda del EV
								else if (pista_EV_lider - j == -1)
								{
									if (qpg_VHC_type(vehiculo_sgte) != n_tipo_Bus1 && qpg_VHC_type(vehiculo_sgte) != n_tipo_Bus2)
									{
										qps_VHC_laneLow(vehiculo_sgte, j);
									}
								}
							}
						}

					}
					else if (qpg_VHC_distance(vehiculo_sgte) > dist_max + distancia_alerta_aguas_arriba + largo_EV && (map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][0] == PTRUE || map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][1] == PTRUE))
					{
						qps_VHC_aggression(vehiculo_sgte, map_agresividades[qpg_VHC_uniqueID(vehiculo_sgte)]);

						qps_VHC_laneRange(vehiculo_sgte, puede_usar_pista_min(vehiculo_sgte,link), puede_usar_pista_max(vehiculo_sgte, link));

						contador_timesteps_intentando_cambiarse_pista[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
						map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PFALSE;
						map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PFALSE;
					}

					else if (qpg_VHC_type(vehiculo_sgte) == n_tipo_EV)
					{
						map_veh_alerta[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PFALSE;
					}
					vehiculo_sgte = qpg_VHC_ahead(vehiculo_sgte);
				}


			}


		}
		
		
		if (n_pistas > 1)
		{
			//link tiene ambos extremos pistas acera o estacionamiento y solo 1 pista mixta
			if (n_pistas == 3 && pista_min == 2 && pista_min==pista_max)
			{
				//ver vehiculos en pista mas cercana a acera
				vehiculo_sgte = qpg_LNK_vehicleTail(link, 2);
				while (vehiculo_sgte != NULL)
				{
					if (es_veh_liviano(vehiculo_sgte) == PTRUE)
					{
						//si no me acabo de intentar subir a vereda y soy un POV liviano
						if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] == PFALSE)
						{
							//si estoy aguas abajo del EV lider, no muy cerca de la interseccion
							if (qpg_VHC_distance(vehiculo_sgte) >= distancia_min_interseccion_modelo_vereda && qpg_VHC_distance(vehiculo_sgte) <= dist_min  && qpg_VHC_distance(vehiculo_sgte) >= dist_min - distancia_alerta_aguas_abajo_vereda)
							{
								//si estoy en una situacion de mucha congestion: he tenido velocidad muy baja promedio ultimamente, ahora estoy detenido y 3 vehiculos adelante estan detenidos: querer subirse a la vereda
								if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] == PFALSE && map_veh_tiene_suficiente_tiempo[qpg_VHC_uniqueID(vehiculo_sgte)].second == PTRUE && qpg_VHC_speed(vehiculo_sgte) < 0.1 && qpg_VHC_ahead(qpg_VHC_ahead(qpg_VHC_ahead(vehiculo_sgte))) != NULL)
								{

									if (qpg_VHC_speed(qpg_VHC_ahead(qpg_VHC_ahead(qpg_VHC_ahead(vehiculo_sgte)))) < 0.1 && promedio(map_velocidades_historicas[qpg_VHC_uniqueID(vehiculo_sgte)].second, segundos_velocidad_historica*timesteps_por_segundo) < velocidad_historica_querer_vereda)
									{
										map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PTRUE;
										contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
										qps_VHC_aggression(vehiculo_sgte, max_agresion);
										if (moneda() == 1)
										{
											qps_VHC_laneRange(vehiculo_sgte, 1, 1);
										}
										else
										{
											qps_VHC_laneRange(vehiculo_sgte, 3, 3);
										}
									}
								}
							}

							//si me quiero subir a vereda entonces
							if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] == PTRUE)
							{
								contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] += 1;
								//si aun no puede subir a la vereda, no seguir intentandolo
								if (contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] >= timesteps_por_segundo*tolerancia_segundos_buscando_subir_vereda)
								{
									qps_VHC_laneRange(vehiculo_sgte, 2, 2);
									qps_VHC_aggression(vehiculo_sgte, map_agresividades[qpg_VHC_uniqueID(vehiculo_sgte)]);
									map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PFALSE;
									map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PTRUE;
									contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
								}
							}


						}
						//volver a intentar subirme a vereda despues de un tiempo
						//else if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] == PTRUE) <-equivalente a else
						else
						{
							contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] += 1;
							if (contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] >= timesteps_por_segundo*tolerancia_segundos_volver_subir_vereda)
							{
								map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PFALSE;
								contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
							}
						}

					}
					vehiculo_sgte = qpg_VHC_ahead(vehiculo_sgte);
				}
			}
			//link tiene alguna pista acera o estacionamiento
			else if(pista_min != 1 || pista_max != n_pistas)
			{
				if (pista_max != n_pistas)
				{
					//si lider esta en pista mas cercana a acera
					if (pista_EV_lider == n_pistas - 1)
					{
						//ver vehiculos en pista mas cercana a acera
						vehiculo_sgte = qpg_LNK_vehicleTail(link, n_pistas - 1);
						while (vehiculo_sgte != NULL)
						{
							if (es_veh_liviano(vehiculo_sgte) == PTRUE)
							{
								//si no me acabo de intentar subir a vereda y soy un POV liviano
								if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] == PFALSE)
								{
									//si estoy aguas abajo del EV lider, no muy cerca de la interseccion
									if (qpg_VHC_distance(vehiculo_sgte) >= distancia_min_interseccion_modelo_vereda && qpg_VHC_distance(vehiculo_sgte) <= dist_min  && qpg_VHC_distance(vehiculo_sgte) >= dist_min - distancia_alerta_aguas_abajo_vereda)
									{
										//si estoy en una situacion de mucha congestion: he tenido velocidad muy baja promedio ultimamente, ahora estoy detenido y 3 vehiculos adelante estan detenidos: querer subirse a la vereda
										if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] == PFALSE && map_veh_tiene_suficiente_tiempo[qpg_VHC_uniqueID(vehiculo_sgte)].second == PTRUE && qpg_VHC_speed(vehiculo_sgte) < 0.1 && qpg_VHC_ahead(qpg_VHC_ahead(qpg_VHC_ahead(vehiculo_sgte))) != NULL)
										{

											if (qpg_VHC_speed(qpg_VHC_ahead(qpg_VHC_ahead(qpg_VHC_ahead(vehiculo_sgte)))) < 0.1 && promedio(map_velocidades_historicas[qpg_VHC_uniqueID(vehiculo_sgte)].second, segundos_velocidad_historica*timesteps_por_segundo) < velocidad_historica_querer_vereda)
											{
												map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PTRUE;
												contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
												qps_VHC_aggression(vehiculo_sgte, max_agresion);
												qps_VHC_laneRange(vehiculo_sgte, n_pistas, n_pistas);
											}
										}
									}

									//si me quiero subir a vereda entonces
									if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] == PTRUE)
									{
										contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] += 1;
										//si aun no puede subir a la vereda, no seguir intentandolo
										if (contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] >= timesteps_por_segundo*tolerancia_segundos_buscando_subir_vereda)
										{
											qps_VHC_laneRange(vehiculo_sgte, puede_usar_pista_min(vehiculo_sgte, link), n_pistas - 1);
											qps_VHC_aggression(vehiculo_sgte, map_agresividades[qpg_VHC_uniqueID(vehiculo_sgte)]);
											map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PFALSE;
											map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PTRUE;
											contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
										}
									}


								}
								//volver a intentar subirme a vereda despues de un tiempo
								//else if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] == PTRUE) <-equivalente a else
								else
								{
									contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] += 1;
									if (contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] >= timesteps_por_segundo*tolerancia_segundos_volver_subir_vereda)
									{
										map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PFALSE;
										contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
									}
								}

							}
							vehiculo_sgte = qpg_VHC_ahead(vehiculo_sgte);
						}
					}
				}

				if (pista_min != 1)
				{
					//si lider esta en pista mas cercana a acera
					if (pista_EV_lider == 2)
					{
						//ver vehiculos en pista mas cercana a acera
						vehiculo_sgte = qpg_LNK_vehicleTail(link, 2);
						while (vehiculo_sgte != NULL)
						{
							if (es_veh_liviano(vehiculo_sgte) == PTRUE)
							{
								//si no me acabo de intentar subir a vereda y soy un POV liviano
								if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] == PFALSE)
								{
									//si estoy aguas abajo del EV lider, no muy cerca de la interseccion
									if (qpg_VHC_distance(vehiculo_sgte) >= distancia_min_interseccion_modelo_vereda && qpg_VHC_distance(vehiculo_sgte) <= dist_min  && qpg_VHC_distance(vehiculo_sgte) >= dist_min - distancia_alerta_aguas_abajo_vereda)
									{
										//si estoy en una situacion de mucha congestion: he tenido velocidad muy baja promedio ultimamente, ahora estoy detenido y 3 vehiculos adelante estan detenidos: querer subirse a la vereda
										if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] == PFALSE && map_veh_tiene_suficiente_tiempo[qpg_VHC_uniqueID(vehiculo_sgte)].second == PTRUE && qpg_VHC_speed(vehiculo_sgte) < 0.1 && qpg_VHC_ahead(qpg_VHC_ahead(qpg_VHC_ahead(vehiculo_sgte))) != NULL)
										{

											if (qpg_VHC_speed(qpg_VHC_ahead(qpg_VHC_ahead(qpg_VHC_ahead(vehiculo_sgte)))) < 0.1 && promedio(map_velocidades_historicas[qpg_VHC_uniqueID(vehiculo_sgte)].second, segundos_velocidad_historica*timesteps_por_segundo) < velocidad_historica_querer_vereda)
											{
												map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PTRUE;
												contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
												qps_VHC_aggression(vehiculo_sgte, max_agresion);
												qps_VHC_laneRange(vehiculo_sgte, 1, 1);
											}
										}
									}

									//si me quiero subir a vereda entonces
									if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] == PTRUE)
									{
										contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] += 1;
										//si aun no puede subir a la vereda, no seguir intentandolo
										if (contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] >= timesteps_por_segundo*tolerancia_segundos_buscando_subir_vereda)
										{
											qps_VHC_laneRange(vehiculo_sgte, 2, puede_usar_pista_max(vehiculo_sgte, link));
											qps_VHC_aggression(vehiculo_sgte, map_agresividades[qpg_VHC_uniqueID(vehiculo_sgte)]);
											map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PFALSE;
											map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PTRUE;
											contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
										}
									}


								}
								//volver a intentar subirme a vereda despues de un tiempo
								//else if (map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] == PTRUE) <-equivalente a else
								else
								{
									contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] += 1;
									if (contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] >= timesteps_por_segundo*tolerancia_segundos_volver_subir_vereda)
									{
										map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PFALSE;
										contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;
									}
								}

							}
							vehiculo_sgte = qpg_VHC_ahead(vehiculo_sgte);
						}
					}
				}
			}
		}

		//Modelo interseccion
		//si es un EV acercandose a una interseccion y no es un link fuente/sumidero y que no sea caso sin interseccion entre 2 links con doble sentido
		if (dist_min <= distancia_modelo_interseccion && map_link_tiene_interseccion[qpg_LNK_index(link)] == PTRUE)
		{
			//ver todos los links "entrantes" a interseccion
			for (int i = 1; i <= qpg_NDE_entryLinks(qpg_LNK_nodeEnd(link)); i++)
			{
				//setear ceder interseccion como true
				map_link_cede_interseccion[qpg_LNK_index(qpg_NDE_linkEntry(qpg_LNK_nodeEnd(link), i))] = PTRUE;
			}
		}

	}//Fin caso link con EV

//A continuacion script se ejecuta con o sin EV
	map_EV_lider_timestep_anterior[qpg_LNK_index(link)] = EV_lider;
	
	
	//Revisar si hay autos en pistas de acera y ya pasaron los EV
	if (pista_min != 1)
	{
		vehiculo_sgte = qpg_LNK_vehicleTail(link, 1);
		while (vehiculo_sgte != NULL && qpg_VHC_distance(vehiculo_sgte) > dist_max + largo_EV)
		{
			map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PFALSE;
			map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PTRUE;
			contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;

			qps_VHC_laneRange(vehiculo_sgte, 2, puede_usar_pista_max(vehiculo_sgte, link));
			qps_VHC_stopped(vehiculo_sgte, PFALSE);
			qps_VHC_changeLane(vehiculo_sgte, 1);

			vehiculo_sgte = qpg_VHC_ahead(vehiculo_sgte);
		}
	}

	if (pista_max != n_pistas)
	{
		vehiculo_sgte = qpg_LNK_vehicleTail(link, n_pistas);
		while (vehiculo_sgte != NULL && qpg_VHC_distance(vehiculo_sgte) > dist_max + largo_EV)
		{
			map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][1] = PFALSE;
			map_veh_quiere_vereda[qpg_VHC_uniqueID(vehiculo_sgte)][0] = PTRUE;
			contador_timesteps_intentando_subirse_vereda[qpg_VHC_uniqueID(vehiculo_sgte)] = 0;

			qps_VHC_laneRange(vehiculo_sgte, puede_usar_pista_min(vehiculo_sgte, link), n_pistas - 1);
			qps_VHC_stopped(vehiculo_sgte, PFALSE);
			qps_VHC_changeLane(vehiculo_sgte, -1);

			vehiculo_sgte = qpg_VHC_ahead(vehiculo_sgte);
		}
	}

}
//Fin funcion llamada cada instante discreto de simulacion sobre cada link


//Funcion llamada cada instante discreto de simulacion sobre cada vehiculo
void qpx_VHC_timeStep(VEHICLE* vehicle){
	//En caso que vehiculo ande por vereda, nunca avanzar como si fuera calzada
	if (qpg_LNK_laneRestriction(qpg_VHC_link(vehicle), qpg_VHC_lane(vehicle)) == -1 || qpg_LNK_laneRestriction(qpg_VHC_link(vehicle), qpg_VHC_lane(vehicle)) == 4)
	{
		if (qpg_VHC_speed(vehicle) > 0)
		{
			qps_VHC_speed(vehicle, 0);
			qps_VHC_stopped(vehicle, PTRUE);
			//si estoy cerca de vereda, cambiarme ahora
			if (qpg_VHC_distance(vehicle) < distancia_min_interseccion_modelo_vereda)
			{
				qps_VHC_stopped(vehicle, PFALSE);
				if (qpg_VHC_lane(vehicle) == 1) {
					qps_VHC_changeLane(vehicle, 1);
				}
				else
				{
					qps_VHC_changeLane(vehicle, -1);
				}
			}
		}
	}

	//Guardar velocidad si vehiculo lleva suficiente tiempo existiendo en simulacion
	if (map_veh_tiene_suficiente_tiempo[qpg_VHC_uniqueID(vehicle)].first == PFALSE && qpg_NET_wholeSeconds() - qpg_VHC_startTime(vehicle) > segundos_velocidad_historica)
	{
		map_veh_tiene_suficiente_tiempo[qpg_VHC_uniqueID(vehicle)].first = PTRUE;
		map_veh_tiene_suficiente_tiempo[qpg_VHC_uniqueID(vehicle)].second = PTRUE;
	}

	//guardar velocidad historica de vehiculo para ultimos 20 timesteps
	map_velocidades_historicas[qpg_VHC_uniqueID(vehicle)].second[map_velocidades_historicas[qpg_VHC_uniqueID(vehicle)].first] = qpg_VHC_speed(vehicle);
	map_velocidades_historicas[qpg_VHC_uniqueID(vehicle)].first += 1;

	if (map_velocidades_historicas[qpg_VHC_uniqueID(vehicle)].first > timesteps_por_segundo*segundos_velocidad_historica - 1)
	{
		map_velocidades_historicas[qpg_VHC_uniqueID(vehicle)].first = 0;
	}
}

//Funcion llamada cuando un vehiculo se mueve
void qpx_VHC_move(VEHICLE* vehicle, LINK* link, float distance, float speed) {

	//si EV estaba cruzando pero ya termino de pasar de un link a otro, volver a la normalidad
	if (qpg_VHC_type(vehicle) == n_tipo_EV && map_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)] == PTRUE && qpg_VHC_onNode(vehicle) == PFALSE)
	{
		//ya no esta cruzando interseccion
		map_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)] = PFALSE;
		//volver links a la normalidad, dejar de ceder paso forzadamente
		for (int i = 1; i <= qpg_NDE_entryLinks(map_link_anterior_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)]); i++)
		{
			map_link_cede_interseccion[qpg_LNK_index(qpg_NDE_linkEntry(map_link_anterior_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)], i))] = PFALSE;
		}
		//borrar nodo que se estaba guardando asociado a EV
		map_link_anterior_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)] = NULL;
	}

	if (qpg_VHC_type(vehicle) != n_tipo_EV && distance <= distancia_modelo_interseccion && qpg_LNK_laneRestriction(link, qpg_VHC_lane(vehicle)) != -1 && qpg_LNK_laneRestriction(link, qpg_VHC_lane(vehicle)) != 4)
	{
		//si debo ceder a EV en interseccion, no soy un EV, estoy cerca de linea de detencion, no estoy en un lane restringido
		if (map_link_cede_interseccion[qpg_LNK_index(link)] == PTRUE) {
			//Avanzar solo:
			//si justo atras hay un vehiculo de emergencia
			if (qpg_VHC_behind(vehicle) != NULL && qpg_VHC_type(qpg_VHC_behind(vehicle)) == n_tipo_EV)
			{
			}
			//si 2 vehiculos atras hay un vehiculo de emergencia
			else if (qpg_VHC_behind(vehicle) != NULL && qpg_VHC_behind(qpg_VHC_behind(vehicle)) != NULL && qpg_VHC_type(qpg_VHC_behind(qpg_VHC_behind(vehicle))) == n_tipo_EV)
			{
			}
			//si no, no cruzar interseccion, detenerse si esta cerca de linea de detencion
			else
			{
				qps_VHC_braking(vehicle, PTRUE);
				qps_VHC_holdTransfer(vehicle, PTRUE);

				if (qpg_VHC_behind(vehicle) != NULL)
				{
					//ver esto, quiza frenado podria ser con algun modelito
					qps_VHC_braking(qpg_VHC_behind(vehicle), PTRUE);
					qps_VHC_speed(qpg_VHC_behind(vehicle), 0.95*qpg_VHC_speed(qpg_VHC_behind(vehicle)));
					qps_VHC_holdTransfer(qpg_VHC_behind(vehicle), PTRUE);
				}
				if (distance < distancia_stop_modelo_interseccion) {
					qps_VHC_stopped(vehicle, PTRUE);
				}
			}
		}
		//si ya paso EV, pasaron timestep timer para volver a normalidad, estoy parado y no estoy en un lane restringido, moverme
		else if (qpg_VHC_stopped(vehicle) == PTRUE)
		{
			qps_VHC_stopped(vehicle, PFALSE);
		}
	}
}

//Funcion llamada cuando un vehiculo se mueve de un arco a otro
void qpx_VHC_transfer(VEHICLE* vehicle, LINK* link1, LINK* link2) {

	//si un EV esta saliendo
	if (qpg_VHC_type(vehicle) == n_tipo_EV)
	{
		//si estaba en un link normal y tenia interseccion y EV esta cruzando interseccion
		if (map_link_tiene_interseccion[qpg_LNK_index(link1)] == PTRUE)
		{
			//no hacer nada aun, seguir cediendole el paso al link1
			//Excepto en 1 casos:
			//si hay otro EV que tambien va a cruzar esta interseccion y esta muy cerca:
			Bool EV_detras_quiere_cruzar = PFALSE;
			for (int i = 0; i < qpg_LNK_lanes(link1); i++)
			{
				vehiculo_sgte = qpg_LNK_vehicleHead(link1, i + 1);
				while (vehiculo_sgte != NULL && qpg_VHC_distance(vehiculo_sgte) <= distancia_modelo_interseccion)
				{
					if (qpg_VHC_type(vehiculo_sgte) == n_tipo_EV)
					{
						EV_detras_quiere_cruzar = PTRUE;
						break;
					}
					vehiculo_sgte = qpg_VHC_behind(vehiculo_sgte);
				}
			}

			//si se da el caso, seguir cediendole el paso al link1
			if (EV_detras_quiere_cruzar == PFALSE)
			{
				//guardar en mapa que EV esta cruzando y el nodo que esta cruzando
				map_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)] = PTRUE;
				map_link_anterior_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)] = qpg_LNK_nodeEnd(link1);
			}
		}
	}
}


void qpx_VHC_laneChange(VEHICLE* vehicle, LINK* link, int lane1, int lane2) {
	//volver a normalidad si se esta volviendo a la calzada desde la acera
	if (qpg_LNK_laneRestriction(link, lane1) == -1 || qpg_LNK_laneRestriction(link, lane1) == 4) {
		qps_VHC_aggression(vehicle, map_agresividades[qpg_VHC_uniqueID(vehicle)]);
	}
}

//Llamado cuando se crea un vehiculo
void qpx_VHC_release(VEHICLE* vehicle) {

	//Alocar y reservar memoria para el vector con velocidades pasadas
	map_velocidades_historicas[qpg_VHC_uniqueID(vehicle)].second.reserve(timesteps_por_segundo*segundos_velocidad_historica);
	map_velocidades_historicas[qpg_VHC_uniqueID(vehicle)].second.resize(timesteps_por_segundo*segundos_velocidad_historica);
	//Guardar su agresividad
	map_agresividades[qpg_VHC_uniqueID(vehicle)] = qpg_VHC_aggression(vehicle);
}

//Llamado cuando vehiculo llega a su destino, liberar memoria asociada
void qpx_VHC_arrive(VEHICLE* vehicle, LINK* link, ZONE* zone) {

	//si EV estaba cruzando pero ya termino de pasar de un link a otro, volver a la normalidad
	if (qpg_VHC_type(vehicle) == n_tipo_EV && map_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)] == PTRUE)
	{
		//ya no esta cruzando interseccion
		map_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)] = PFALSE;
		//volver links a la normalidad, dejar de ceder paso forzadamente
		for (int i = 1; i <= qpg_NDE_entryLinks(map_link_anterior_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)]); i++)
		{
			map_link_cede_interseccion[qpg_LNK_index(qpg_NDE_linkEntry(map_link_anterior_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)], i))] = PFALSE;
		}
		//borrar nodo que se estaba guardando asociado a EV
		map_link_anterior_EV_cruzando_interseccion[qpg_VHC_uniqueID(vehicle)] = NULL;
	}

	map_veh_alerta.erase(qpg_VHC_uniqueID(vehicle));
	map_agresividades.erase(qpg_VHC_uniqueID(vehicle));
	contador_timesteps_intentando_cambiarse_pista.erase(qpg_VHC_uniqueID(vehicle));
	map_veh_quiere_vereda.erase(qpg_VHC_uniqueID(vehicle));
	contador_timesteps_intentando_subirse_vereda.erase(qpg_VHC_uniqueID(vehicle));
	map_velocidades_historicas.erase(qpg_VHC_uniqueID(vehicle));
	map_EV_cruzando_interseccion.erase(qpg_VHC_uniqueID(vehicle));
	map_veh_tiene_suficiente_tiempo.erase(qpg_VHC_uniqueID(vehicle));
}