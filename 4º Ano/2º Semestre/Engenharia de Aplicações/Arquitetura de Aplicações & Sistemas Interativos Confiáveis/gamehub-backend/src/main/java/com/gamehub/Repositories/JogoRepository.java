package com.gamehub.Repositories;

import com.gamehub.Model.Posts.Jogo;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;

import java.util.List;

public interface JogoRepository extends CrudRepository<Jogo, Integer> {

    String FIND_Most_Popular = "select id, ano_lancamento, banner_link, desenvolvedora, faixa_etaria, nome from jogo as j inner join jogos as js on j.id = js.jogo Group by jogo order by count(jogo) DESC limit :max";

    @Query(value = FIND_Most_Popular, nativeQuery = true)
    List<Jogo> findMostPopular(@Param("max") int limit);

    String getJogosPorSeguir = "SELECT * FROM jogo WHERE id NOT IN (SELECT jogo FROM jogos WHERE gamer=:gamer_id)";

    @Query(value = getJogosPorSeguir, nativeQuery = true)
    List<Jogo> getJogosPorSeguir(@Param("gamer_id") int gamer_id);

    String getLinkJogos = "SELECT banner_link from jogo where nome=:nomeJogo";

    @Query(value = getLinkJogos, nativeQuery = true)
    String getLinkBannerJogo(@Param("nomeJogo") String nomeJogo);

    String getSeguidores = "SELECT count(gamer) FROM jogos WHERE jogo=:jogoId";

    @Query(value = getSeguidores, nativeQuery = true)
    int getNumSeguidores(@Param("jogoId") int jogoId);
}
